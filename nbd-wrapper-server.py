#!/usr/bin/env python
# -*- coding: utf-8 -*-

'''
nbd-wrapper-server: exports removable media by configuring a nbd-server.
Copyright (C) 2014  Juan Carlos Rodrigo

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
'''

__version__ = '0.0.3'
__author__ = 'Juan Carlos Rodrigo'
__copyright__ = '(C) 2014 Juan Carlos Rodrigo'

import os, fcntl, optparse, signal, subprocess, pwd, grp
import sys, time, atexit, socket, threading, re
try:
    import configparser
except ImportError:
    import ConfigParser as configparser
try:
    from subprocess import DEVNULL
except ImportError:
    DEVNULL = open(os.devnull, 'wb')
try:
    from BaseHTTPServer import HTTPServer
    from BaseHTTPServer import BaseHTTPRequestHandler
except ImportError:
    from http.server import HTTPServer
    from http.server import BaseHTTPRequestHandler
try:
    import urlparse
except ImportError:
    import urllib.parse as urlparse
try:
    ProcessLookupError
except NameError:
    ProcessLookupError = OSError

DEF_NBD_SERVER = '/usr/bin/nbd-server'
DEF_NBD_PID_FILE = '/var/run/nbd-wrapper-server.pid'
DEF_OWN_PID_FILE = '/var/run/nbd-wrapper-own.pid'
DEF_LOCK_FILE = '/var/run/nbd-wrapper.lock'
DEF_CONFIG_FILE = '/var/run/nbd-wrapper.conf'
DEF_WAIT_DEVICE = 10
DEF_OWN_PORT = 4097
DEF_OWN_ADDRESS = ''

RE_KEY_VALUE = re.compile(r'^\s*(?P<key>[^=]+)\s*=\s*(?P<value>.*?)\s*$')
QS_SLEEP = 'sleep'
FALSE, TRUE = ('false', 'true')
DEV_ZERO = '/dev/zero'
DEV_NULL = '/dev/null'
SECTION_GENERIC = 'generic'
SECTION_DEV_ZERO = DEV_ZERO
KEY_OLD_STYLE = 'oldstyle'
KEY_ALLOW_LIST = 'allowlist'
KEY_EXPORT_NAME = 'exportname'
KEY_READ_ONLY = 'readonly'
WAIT_INTERVAL = 0.05
EXPORT_MARK = 'export:'
CONTENT_TYPE = 'Content-type'
TEXT_PLAIN = 'text/plain'
OK_200 = 200
ADD, REMOVE = range(2)
REDUCE_SLEEP = 0.8
NBD_WRAPPER_USER = 'nbdwrap'
NBD_WRAPPER_GROUP = NBD_WRAPPER_USER
KEY_MEDIA = '_media'
DEFAULT_MEDIA = 'ID_DRIVE_FLASH'

# These are the UDEV rules used to launch the wrapper when devices become
# present and remove them when they are unplugged or ejected
UDEV_RULES = '''\
# CDROM/DVD rules
ACTION=="change", SUBSYSTEM=="block", KERNEL=="sr[0-9]*|xvd*", ENV{DEVTYPE}=="disk", ENV{ID_FS_USAGE}=="?*", ENV{DISK_MEDIA_CHANGE}=="?*", GROUP="%(group)s", MODE="0660", RUN+="%(wrapper_sh)s --add /dev/%%k _media=ID_CDROM readonly=true"
ACTION=="change", SUBSYSTEM=="block", KERNEL=="sr[0-9]*|xvd*", ENV{DEVTYPE}=="disk", ENV{DISK_EJECT_REQUEST}=="?*", RUN+="%(wrapper_sh)s --remove /dev/%%k"
ACTION=="change", SUBSYSTEM=="block", KERNEL=="sr[0-9]*|xvd*", ENV{DEVTYPE}=="disk", ENV{ID_FS_USAGE}=="", RUN+="%(wrapper_sh)s --remove /dev/%%k"
# Floppy disk rules
ACTION=="change", SUBSYSTEM=="block", ENV{ID_TYPE}=="floppy", ENV{DEVTYPE}=="disk", ENV{ID_FS_USAGE}=="?*", GROUP="%(group)s", MODE="0660", RUN+="%(wrapper_sh)s --add /dev/%%k _media=ID_DRIVE_FLOPPY sync=true flush=true"
ACTION=="change", SUBSYSTEM=="block", ENV{ID_TYPE}=="floppy", ENV{DEVTYPE}=="disk", ENV{ID_FS_USAGE}=="", RUN+="%(wrapper_sh)s --remove /dev/%%k"
# USB disk rules
ACTION=="add", SUBSYSTEM=="block", ENV{ID_PATH}=="*-usb-*", ENV{DEVTYPE}=="disk", GROUP="%(group)s", MODE="0660", RUN+="%(wrapper_sh)s --add /dev/%%k _media=ID_DRIVE_FLASH sync=true flush=true"
ACTION=="remove", SUBSYSTEM=="block", ENV{ID_PATH}=="*-usb-*", ENV{DEVTYPE}=="disk", RUN+="%(wrapper_sh)s --remove /dev/%%k"
'''

# Helper shell used to start the wrapper server from UDEV
UDEV_SHELL = '''\
#!/bin/sh
%(wrapper_py)s%(nbd)s%(cfg)s%(lock)s%(nbd_pid)s%(own_pid)s%(wait)s%(address)s%(port)s $*&
'''

def locked(f):
    'This decorator locks a file before calling the decorated function.'
    def dec(self, *args):
        lock = open(self.lock_file, 'w')
        fcntl.lockf(lock, fcntl.LOCK_EX)
        return f(self, *args)
    return dec

class QueryHandler(BaseHTTPRequestHandler):
    'This class serves the nbd configuration file to the nbd-wrapper clients.'

    def log_request(self, *args): pass
    def log_error(self, *args): pass
    def log_message(self, *args): pass

    @property
    def lock_file(self):
        'Returns the lock_file attribute, used by the lock decorator'
        return self.server.lock_file

    @locked
    def _read_config(self):
        'Read the nbd configuration file (locked)'
        return open(self.server.config_file, 'rb').read()

    def do_GET(self):
        '''Returns the nbd-server configuration file to the
        nbd-wrapper client. If the nbd-wrapper passes the sleep
        query string parameter we sleep until the given time has passed
        or return at once reading the latest configuration file.
        This scheme avoids a busy poll on the client and at the
        same time serves the 'plug' and 'unplug' events with no delay.'''
        query_string = urlparse.parse_qs(
            urlparse.urlparse(self.path).query)
        self.send_response(OK_200)
        self.send_header(CONTENT_TYPE, TEXT_PLAIN)
        self.end_headers()
        try:
            # Sleep if the nbd-wrapper client has requested todo so
            sleep = float(query_string[QS_SLEEP][0])
            self.server.event.wait(sleep * REDUCE_SLEEP)
            self.server.event.clear()
        except (AttributeError, ValueError, KeyError):
            pass
        try:
            # Send the ndb-server configuration file to the client
            config = self._read_config()
            self.wfile.write(config)
        except (OSError, IOError):
            pass

class ExportServer(HTTPServer):
    '''This is the HTTP server that provides an up-to-date nbd
    configuration file to the remove ndb-wrapper client.'''

    def __init__(self, worker, server_address,
                 config_file, pid_file, lock_file):
        self.worker = worker
        self.pid_file = pid_file
        self.config_file = config_file
        self.lock_file = lock_file
        self.event = threading.Event()
        self.event.clear()
        self.leave = False
        self.allow_reuse_address = True
        self.daemonize()
        HTTPServer.__init__(self, server_address, QueryHandler)
        self.run()

    def daemonize(self):
        'Daemonizes the HTTP server'
        try:
            pid = os.fork()
            if pid > 0: sys.exit(0)
        except OSError:
            sys.exit(1)

        os.chdir('/')
        os.setsid()
        os.umask(0o007)

        try:
            pid = os.fork()
            if pid > 0: sys.exit(0)
        except OSError:
            sys.exit(1)

        sys.stdout.flush()
        sys.stderr.flush()
        stdin = open(DEV_NULL, 'r')
        stdout = open(DEV_NULL, 'a+')
        stderr = open(DEV_NULL, 'a+')
        os.dup2(stdin.fileno(), sys.stdin.fileno())
        os.dup2(stdout.fileno(), sys.stdout.fileno())
        os.dup2(stderr.fileno(), sys.stderr.fileno())

        signal.signal(signal.SIGTERM, self.signal_term)
        signal.signal(signal.SIGHUP, self.signal_hup)
        atexit.register(self.stop)
        open(self.pid_file, 'w+').write('%d\n' % os.getpid())

    def stop(self):
        'Stops the nbd server and removes the pid file'
        self.worker.stop_server()
        try: os.remove(self.pid_file)
        except (OSError, IOError): pass

    def signal_term(self, signal, frame):
        'Handles the TERM signal by stopping nbd wrapper'
        self.leave = True
        self.event.set()
        self.server_close()

    def signal_hup(self, signal, frame):
        'Handles the HUP signal by unblocking the watiting HTTP client'
        self.event.set()

    def run(self):
        'Handles HTTP requests until the TERM signal is received'
        try:
            while not self.leave:
                self.handle_request()
        except (socket.error, ValueError):
            pass

class Server(object):
    '''This class:
        + Creates a default configuration file if needed.
        + Handles the nbd server operations (start, stop, reload).
        + Updates the configuration to add and remove exports.'''
    def __init__(self,
                 config_file=DEF_CONFIG_FILE,
                 lock_file=DEF_LOCK_FILE,
                 nbd_pid_file=DEF_NBD_PID_FILE,
                 own_pid_file=DEF_OWN_PID_FILE,
                 nbd_server_binary=DEF_NBD_SERVER,
                 wait_device=DEF_WAIT_DEVICE,
                 own_address=(DEF_OWN_ADDRESS, DEF_OWN_PORT),
                 export_options=dict()):
        self.config_file = config_file
        self.lock_file = lock_file
        self.nbd_pid_file = nbd_pid_file
        self.own_pid_file = own_pid_file
        self.nbd_server_binary = nbd_server_binary
        self.wait_device = wait_device
        self.own_address = own_address
        self.export_options = export_options
        self._nbd_pid = None
        self._own_pid = None

    @property
    def nbd_pid(self):
        'Returns the current server pid from the nbd-server pid file'
        if self._nbd_pid == None:
            try:
                self._nbd_pid = int(
                    open(self.nbd_pid_file, 'r').read().strip())
            except (ValueError, OSError, IOError):
                pass
        return self._nbd_pid

    @property
    def own_pid(self):
        'Returns the HTTP server pid (our own pid)'
        if self._own_pid == None:
            try:
                self._own_pid = int(
                    open(self.own_pid_file, 'r').read().strip())
            except (ValueError, OSError, IOError):
                pass
        return self._own_pid

    def _wait_device(self, device):
        'Waits for the block device to come up'
        stop_time = time.time() + self.wait_device
        while time.time() < stop_time:
            try:
                if os.path.exists(device):
                    return True
                time.sleep(WAIT_INTERVAL)
            except (OSError, IOError):
                pass
        return False

    def _safe_start(self, pid, callback):
        'Start a daemon (via the callback) if it is not running'
        if pid == None:
            callback()
        else:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                callback()

    def _default_config(self):
        'Create a default nbd config file and remove stalled exports'
        cfg = configparser.ConfigParser()
        try: cfg.read(self.config_file)
        except configparser.Error: pass

        # Create the default section if it does not exist
        if not cfg.has_section(SECTION_GENERIC):
            cfg.add_section(SECTION_GENERIC)
        cfg.set(SECTION_GENERIC, KEY_ALLOW_LIST, TRUE)
        cfg.set(SECTION_GENERIC, KEY_OLD_STYLE, FALSE)

        # Create the /dev/zero section if it does not exist
        if not cfg.has_section(SECTION_DEV_ZERO):
            cfg.add_section(SECTION_DEV_ZERO)
        cfg.set(SECTION_DEV_ZERO, KEY_EXPORT_NAME, DEV_ZERO)
        cfg.set(SECTION_DEV_ZERO, KEY_READ_ONLY, TRUE)

        # Remove stalled exports
        mark_len = len(EXPORT_MARK)
        for section in cfg.sections():
            if section[:mark_len] == EXPORT_MARK:
                try:
                    device = cfg.get(section, KEY_EXPORT_NAME)
                    if not os.path.exists(device):
                        cfg.remove_section(section)
                except configparser.NoOptionError:
                    pass

        return cfg

    def _touch_run_files(self):
        'Creates the /var/run files and gives the nbdwrap user access to them'
        gid = grp.getgrnam(NBD_WRAPPER_GROUP).gr_gid
        for file_name in (self.config_file, self.lock_file,
                          self.nbd_pid_file, self.own_pid_file):
            try:
                f = open(file_name, 'a+')
                os.fchown(f.fileno(), 0, gid)
                os.fchmod(f.fileno(), 0o660)
                f.close()
            except (OSError, IOError):
                pass

    def _drop_privileges(self):
        'Drop user privileges to the nbbwrap user and group'
        os.setgroups([])
        os.setgid(grp.getgrnam(NBD_WRAPPER_GROUP).gr_gid)
        os.setuid(pwd.getpwnam(NBD_WRAPPER_USER).pw_uid)
        os.umask(0o077)

    def _configure(self):
        'Prepare a default config file and run the server (unlocked)'
        # Create the unprivileged files in /var/run
        self._touch_run_files()
        # Drop privileges
        self._drop_privileges()
        # Read the config file
        return self._default_config()

    def _start(self):
        'Run the servers if needed'
        self._safe_start(self.nbd_pid, self._run_nbd_server)
        self._safe_start(self.own_pid, self._run_own_server)

    def _update_config(self, device, op):
        'Update the config file adding or removing the devices (unlocked)'
        cfg = self._configure()
        section = '%s%s' % (EXPORT_MARK, device)
        has_section = cfg.has_section(section)
        if op == ADD:
            if not has_section:
                cfg.add_section(section)
                cfg.set(section, KEY_EXPORT_NAME, device)
                for key in self.export_options.keys():
                    cfg.set(section, key, self.export_options[key])
            if self._wait_device(device):
                cfg.write(open(self.config_file, 'w'))
                self._reload_nbd()
                self._reload()
        elif op == REMOVE:
            if has_section:
                cfg.remove_section(section)
            cfg.write(open(self.config_file, 'w'))
            self._reload()
        self._start()

    def _run_nbd_server(self):
        'Start the nbd server and save the pid (unlocked)'
        self._nbd_pid = None
        return subprocess.Popen([self.nbd_server_binary,
                                '-C', self.config_file,
                                '-p', self.nbd_pid_file],
                                stdout=DEVNULL, stderr=DEVNULL,
                                close_fds=True).wait()

    def _run_own_server(self):
        'Start the exports HTTP server save the pid (unlocked)'
        self._own_pid = None
        ExportServer(self, self.own_address, self.config_file,
                      self.own_pid_file, self.lock_file)

    def _reload_nbd(self):
        'Reload the nbd server configuration by signaling a HUP (unlocked)'
        try:
            if self.nbd_pid != None:
                os.kill(self.nbd_pid, signal.SIGHUP)
        except ProcessLookupError:
            pass

    def _reload(self):
        'Reload the HTTP server by signaling a HUP (unlocked)'
        try:
            if self.own_pid != None:
                os.kill(self.own_pid, signal.SIGHUP)
        except ProcessLookupError:
            pass

    def stop_server(self):
        'Stop the nbd server, called from atexit (unlocked)'
        if self.nbd_pid != None:
            try:
                os.kill(self.nbd_pid, signal.SIGTERM)
            except ProcessLookupError:
                pass

    def stop(self):
        'Stop the server if it is alive (unlocked)'
        if self.own_pid != None:
            try:
                os.kill(self.own_pid, signal.SIGTERM)
            except ProcessLookupError:
                pass

    @locked
    def start(self):
        'Prepare a default config file and run the server (locked)'
        cfg = self._configure()
        cfg.write(open(self.config_file, 'w'))
        self._start()

    @locked
    def add(self, device):
        'Add a device to the config file and HUP the nbd-server (locked)'
        self._update_config(device, ADD)

    @locked
    def remove(self, device):
        'Remove a device from the config file (locked)'
        self._update_config(device, REMOVE)

def parse_options(args):
    'Parse any custom key=value options for the nbd-server'
    export_options = {KEY_MEDIA: DEFAULT_MEDIA}
    for arg in args:
        m = RE_KEY_VALUE.match(arg)
        if m != None:
            export_options[m.group('key')] = m.group('value')
        else:
            sys.stderr.write('bad option %s should be key=value\n' % arg)
    return export_options

def install(options):
    '''Installs this software by:

        + Creating an unprivileged user
        + Copying this python into /usr/local/bin
        + Creating a shell wrapper for UDEV into /usr/local/bin
        + Installing the UDEV rules into /etc/udev/rules.d

        This installer does not change any existing system files.
    '''
    re_extension = re.compile(r'(\.[^\.]+)*$')
    udev_base = '/etc/udev/rules.d'
    base = '/usr/local/bin'
    home = '/dev/null'
    no_login = '/sbin/nologin'
    user = NBD_WRAPPER_USER
    group = NBD_WRAPPER_GROUP
    src_py = os.path.abspath(sys.argv[0])
    prog_py = os.path.split(src_py)[1]
    wrapper_py = os.path.join(base, prog_py)
    wrapper_sh = re_extension.sub('.sh', wrapper_py)
    udev_rules = os.path.join(
        udev_base, '99-%s' % re_extension.sub('.rules', prog_py))

    # Configure the server's UDEV shell options
    server_options = {'wrapper_py': wrapper_py, 'wrapper_sh': wrapper_sh,
                      'user': user, 'group': group,
                      'nbd': '', 'cfg': '', 'lock': '', 'nbd_pid': '',
                      'own_pid': '', 'wait': '', 'address': '', 'port': ''}
    if options.nbd_server_binary != DEF_NBD_SERVER:
        server_options['nbd'] = " -S '%s'" % options.nbd_server_binary
    if options.config_file != DEF_CONFIG_FILE:
        server_options['config'] = " -C '%s'" % options.config_file
    if options.lock_file != DEF_LOCK_FILE:
        server_options['lock'] = " -L '%s'" % options.lock_file
    if options.nbd_pid_file != DEF_NBD_PID_FILE:
        server_options['nbd_pid'] = " -N '%s'" % options.nbd_pid_file
    if options.own_pid_file != DEF_OWN_PID_FILE:
        server_options['own_pid'] = " -O '%s'" % options.own_pid_file
    if options.wait_device != DEF_WAIT_DEVICE:
        server_options['wait'] = " -D %d" % options.wait_device
    if options.own_server_address != DEF_OWN_ADDRESS:
        server_options['address'] = " -A '%s'" % options.own_server_address
    if options.own_server_port != DEF_OWN_PORT:
        server_options['port'] = " -P %d" % options.own_server_port

    if not os.path.isdir(udev_base):
        sys.stderr.write(
            'ERROR: The UDEV rules directory %s does not exists.\n' \
            'Is UDEV installed on this system?\n' % udev_base)
        return 10

    if not os.path.exists(options.nbd_server_binary):
        sys.stderr.write(
            'ERROR: The binary file %s does not exists.\n' \
            'Please, specify the option --nbd-server-binary ' \
            'pointing to the nbd server binary.\n' % options.nbd_server_binary)
        return 11

    # Create an unprivileged group and user
    try:
        grp.getgrnam(NBD_WRAPPER_GROUP)
    except KeyError:
        os.system("groupadd -r '%s'" % group)
    try:
        pwd.getpwnam(NBD_WRAPPER_USER)
    except KeyError:
        os.system("useradd -r -g '%s' -s '%s' -d '%s' '%s'" % (
            group, no_login, home, user))
    print("user '%s' and group '%s' ready." % (user, group))

    # Install the server wrapper
    try: os.makedirs(base, 755)
    except OSError: pass
    if os.path.isdir(base):
        try:
            f = open(src_py, 'r')
            data = f.read()
            f.close()
            f = open(wrapper_py, 'w')
            os.fchown(f.fileno(), 0, 0)
            os.fchmod(f.fileno(), 0o755)
            f.write(data)
            f.close()
            print('file %s ready.' % wrapper_py)
        except (OSError, IOError):
            sys.stderr.write(
                'ERROR: Cannot write the file %s, ' \
                'you should run the installer as root.\n' % wrapper_py)
            return 11
    else:
        sys.stderr.write(
            'ERROR: Cannot find the directory %s, ' \
            'you should run the installer as root.\n' % base)
        return 11

    # Create the wrapper's UDEV shell
    try:
        f = open(wrapper_sh, 'w')
        os.fchown(f.fileno(), 0, 0)
        os.fchmod(f.fileno(), 0o755)
        f.write(UDEV_SHELL % server_options)
        f.close()
        print('file %s ready.' % wrapper_sh)
    except (OSError, IOError):
        sys.stderr.write(
            'ERROR: Cannot write %s, ' \
            'you should run the installer as root.\n' % wrapper_sh)
        return 12

    # Install the UDEV rules
    try:
        f = open(udev_rules, 'w')
        os.fchown(f.fileno(), 0, 0)
        os.fchmod(f.fileno(), 0o644)
        f.write(UDEV_RULES % server_options)
        f.close()
        os.system('udevadm control --reload')
        print('file %s ready.' % udev_rules)
    except (OSError, IOError):
        sys.stderr.write(
            'ERROR: Cannot write %s, ' \
            'you should run the installer as root.\n' % udev_rules)
        return 13

    print('''
You can add these lines to the syslog-ng.conf file just under the
"source src {...}" section because the nbd-server could get very verbose:

 destination discard {
    file("/dev/null" perm(0666) dir_perm(0755) create_dirs(no));
 };
 filter nbd { program("nbd_server"); };
 log { source(src); filter(nbd); destination(discard); flags(final); };
''')

    return 0

def main():
    parser = optparse.OptionParser(description='''\
%prog: exports removable media by configuring a nbd-server.
Copyright (C) 2014  Juan Carlos Rodrigo
This program comes with ABSOLUTELY NO WARRANTY.
This is free software, and you are welcome to redistribute it
under certain conditions.''', version='%%prog %s' % __version__)
    parser.add_option('-s', '--start', dest='start', action='store_true',
                        default=False, help='start the server')
    parser.add_option('-k', '--stop', dest='stop', action='store_true',
                        default=False, help='stop the server')
    parser.add_option('-a', '--add', dest='add', action='store',
                        default=None, help='export a device using nbd')
    parser.add_option('-r', '--remove', dest='remove', action='store',
                        default=None,
                        help='remove device from the nbd exports')
    parser.add_option('-A', '--own-server-address', dest='own_server_address',
                        action='store', default=DEF_OWN_ADDRESS,
                        help='the nbd-wrapper server address')
    parser.add_option('-P', '--own-server-port', dest='own_server_port',
                        action='store', type="int", default=DEF_OWN_PORT,
                        help='the nbd-wrapper server port')
    parser.add_option('-S', '--nbd-server-binary', dest='nbd_server_binary',
                        action='store', default=DEF_NBD_SERVER,
                        help='the nbd-server binary file')
    parser.add_option('-C', '--cfg', dest='config_file', action='store',
                        default=DEF_CONFIG_FILE,
                        help='the ndb-server configuration file')
    parser.add_option('-L', '--lock', dest='lock_file', action='store',
                        default=DEF_LOCK_FILE,
                        help='lock file serializing parallel actions')
    parser.add_option('-N', '--nbd-pid-file', dest='nbd_pid_file',
                        action='store', default=DEF_NBD_PID_FILE,
                        help='the pid file for nbd-server')
    parser.add_option('-O', '--own-pid-file', dest='own_pid_file',
                        action='store', default=DEF_OWN_PID_FILE,
                        help='the pid file for the nbd-wrapper server')
    parser.add_option('-D', '--wait-device', dest='wait_device',
                        action='store', type="int", default=DEF_WAIT_DEVICE,
                        help='waits this time, in seconds, for devices')
    parser.add_option('-I', '--install', dest='install', action='store_true',
                        default=False,
                        help='installs this software')
    (options, args) = parser.parse_args()

    ret = 0
    if options.add != None or options.remove != None \
        or options.start or options.stop:
        worker = Server(options.config_file, options.lock_file,
                        options.nbd_pid_file, options.own_pid_file,
                        options.nbd_server_binary, options.wait_device,
                        (options.own_server_address,
                            options.own_server_port),
                        parse_options(args))
        if options.add != None:
            worker.add(options.add)
        elif options.remove != None:
            worker.remove(options.remove)
        elif options.start:
            worker.start()
        elif options.stop:
            worker.stop()
    elif options.install:
        ret = install(options)
        print('installation finished ok.' if ret == 0 \
                else 'the installation did not finish, check the error.')
    else:
        parser.print_help()
        ret = 1
    sys.exit(ret)

if __name__ == '__main__':
    main()
