#!/usr/bin/env python
# -*- coding: utf-8 -*-

'''
nbd-wrapper-client: handles remote media using nbd-client processes.
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

__version__ = '0.0.2'
__author__ = 'Juan Carlos Rodrigo'
__copyright__ = '(C) 2014 Juan Carlos Rodrigo'

import optparse, signal, subprocess, threading, pwd
import re, os, sys, glob, time, socket
import multiprocessing as mp
try:
    from subprocess import DEVNULL
except ImportError:
    DEVNULL = open(os.devnull, 'wb')
try:
    import configparser
except ImportError:
    import ConfigParser as configparser

DEF_POLL_INTERVAL = 60
DEF_EXPORTS_PORT = 4097
DEF_NBD_TIMEOUT = 5
DEF_BLOCK_SIZES = ['512', '1024', '2048', '4096']
DEF_BLOCK_SIZE = '1024'
DEF_NBD_CLIENT = '/usr/sbin/nbd-client'
DEF_UDEVADM = '/bin/udevadm'
DEF_PID_FILE = '.nbd-wrapper.pid'

ERROR_WAIT = 1
ENCODING = 'utf-8'
QS_SLEEP = 'sleep'
HTTP_GET = 'GET /%s HTTP/1.1\r\n\r\n'
HTTP_GET_START = HTTP_GET % ''
HTTP_GET_SLEEP = HTTP_GET % ('?%s=%%d' % QS_SLEEP)
EXPORT_MARK = 'export:'
NBD_DEVICES_GLOB = '/dev/nbd*'
RE_NBD_DEVICE = re.compile(r'^.*?/nbd\d+$')
PLUGDEV_GROUP = 'plugdev'
SUDO_GID = 'SUDO_GID'
SUDO_UID = 'SUDO_UID'
HOME = 'HOME'

# These are the UDEV rules required for the system to work.
# The nbd devices are excluded on the default UDEV rules so we need
# all this rules to get the partitions parsed on nbd block devices
UDEV_RULES = '''\
# treat nbd devices as normal devices by reading its partitions
KERNEL!="nbd*", GOTO="persistent_storage_end_nbd"
# no action if removing the device
ACTION=="remove", GOTO="persistent_storage_end_nbd"
# enable in-kernel media-presence polling, poll often the disk can dissapear without warning
ACTION=="add", SUBSYSTEM=="module", KERNEL=="block", ATTR{parameters/events_dfl_poll_msecs}="500"
SUBSYSTEM!="block", GOTO="persistent_storage_end_nbd"
# skip rules for inappropriate block devices
ENV{UDISKS_AUTO}:="0", ENV{UDISKS_IGNORE}:="0", ENV{UDISKS_SYSTEM}:="0"
ENV{DEVTYPE}=="disk", ENV{ID_VENDOR}:="nbd", ENV{ID_SERIAL}:="%k", ENV{ID_DRIVE_FLASH}:="1"
# ignore partitions that span the entire disk
TEST=="whole_disk", GOTO="persistent_storage_end_nbd"
# for partitions import parent information
ENV{DEVTYPE}=="partition", IMPORT{parent}="ID_*"
IMPORT{builtin}="blkid"
# watch metadata changes by tools closing the device after writing
OPTIONS+="watch"
# by-label/by-uuid links (filesystem metadata)
ENV{ID_FS_USAGE}=="filesystem|other|crypto", ENV{ID_FS_UUID_ENC}=="?*", SYMLINK+="disk/by-uuid/$env{ID_FS_UUID_ENC}"
ENV{ID_FS_USAGE}=="filesystem|other", ENV{ID_FS_LABEL_ENC}=="?*", SYMLINK+="disk/by-label/$env{ID_FS_LABEL_ENC}"
# by-partlabel/by-partuuid links (partition metadata)
ENV{ID_PART_ENTRY_SCHEME}=="gpt", ENV{ID_PART_ENTRY_UUID}=="?*", SYMLINK+="disk/by-partuuid/$env{ID_PART_ENTRY_UUID}"
ENV{ID_PART_ENTRY_SCHEME}=="gpt", ENV{ID_PART_ENTRY_NAME}=="?*", SYMLINK+="disk/by-partlabel/$env{ID_PART_ENTRY_NAME}"
# add symlink to GPT root disk
ENV{ID_PART_ENTRY_SCHEME}=="gpt", ENV{ID_PART_GPT_AUTO_ROOT}=="1", SYMLINK+="gpt-auto-root"
# skip rules for inappropriate nbd devices
LABEL="persistent_storage_end_nbd"
'''

# This is the xinit script that launches the nbd wrapper client only for
# remote X sessions. That is when the display is not empty and seems to be
# an IP address.
XINIT_CLIENT = '''\
#!/bin/sh
server=`echo $DISPLAY | cut -d : -f 1`
echo -n "$server" | grep '^[12][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\.[12][0-9]*$' &>/dev/null
[ $? == 0 ] && sudo %(wrapper_sh)s "$server"
'''

# This shell simplifies the sudoers rule and ensures that the nbd wrapper
# client will be called only with the appropiate parameters.
SAFE_SHELL = '''\
#!/bin/sh
echo -n "$1" | grep '^[12][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\.[12][0-9]*$' &>/dev/null
[ $? == 0 ] && %(wrapper_py)s -s "$1" %(port)s%(timeout)s%(nbd)s%(udev)s%(interval)s%(block)s%(pid)s&
'''

# Currently it is impossible to use the nbd-client binary without root
# permissions, nbd-client uses ioctls on the nbd block devices and
# users without system capabilities are disallowed on the nbd Kernel module.
# This sudoers line exactly matches the safe shell command above.
SUDOERS_LINE = '''\
%%%(plugdev)s ALL = NOPASSWD: %(wrapper_sh)s [12]*.[0-9]*.[0-9]*.[12]*
'''

# We need a shutdown script either in
# /etc/kde/shutdown or /etc/gdm/PostSession/Default
SHUTDOWN_SHELL = '''\
#!/bin/sh
kill -TERM `cat "$HOME/%(xpid)s"`
'''

class Stopper(threading.Thread):
    'This class waits for the '
    def __init__(self, worker, queue):
        threading.Thread.__init__(self)
        self.worker = worker
        self.queue = queue
        self.start()

    def run(self):
        self.queue.get()
        self.worker.stop()

class Worker(mp.Process):
    '''This class does the privileged work as root, because
    nbd-client and udevadm depend on root permissions.
    It makes GET petitions to the exports HTTP server on the server
    machine and starts or stops nbd-clients on demand.'''
    def __init__(self, queue, server,
                 port=DEF_EXPORTS_PORT,
                 nbd_timeout=DEF_NBD_TIMEOUT,
                 nbd_client_binary=DEF_NBD_CLIENT,
                 udevadm_binary=DEF_UDEVADM,
                 poll_interval=DEF_POLL_INTERVAL,
                 block_size=DEF_BLOCK_SIZE):
        mp.Process.__init__(self)
        self.queue = queue
        self.server = server
        self.port = port
        self.nbd_timeout = nbd_timeout
        self.exports_addr = (self.server, self.port)
        self.nbd_client_binary = nbd_client_binary
        self.udevadm_binary = udevadm_binary
        self.poll_interval = poll_interval
        self.block_size = block_size
        #
        self.started = False
        self.leave = False
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.devices = [dev for dev in glob.glob(NBD_DEVICES_GLOB)
                                if RE_NBD_DEVICE.match(dev)]
        self.exports = dict()
        self.error_wait = threading.Event()
        self.error_wait.clear()
        self.start()

    def stop(self):
        'Stop the process, close the HTTP socket and stop the loop'
        self.error_wait.set()
        self.leave = True
        try:
            self.socket.shutdown(socket.SHUT_RDWR)
            self.socket.close()
        except socket.error:
            pass

    def _stop_clients(self):
        'Stop the client, kill all the nbd-client processes.'
        # Stop all the nbd-client processes controlled by us
        # Trigger udev rules if needed
        exports = list(self.exports.keys())
        for export in exports:
            self._do_remove(export)
        self.started = False

    def _add(self, export, device):
        'Add an export to the internal structures.'
        self.devices.remove(device)
        self.exports[export] = device

    def _remove(self, export):
        'Remove the export from the internal structures.'
        device = None
        try:
            device = self.exports.pop(export)
            self.devices.append(device)
        except KeyError:
            pass
        return device

    def _do_add(self, export):
        '''add an export: get a free device, run the nbd-client,
        trigger the udev rule and store the export as using the
        found device.'''

        # look for a free device
        for device in self.devices:
            # check if its in use
            if subprocess.Popen([self.nbd_client_binary, '-c', device],
                                stdout=DEVNULL, stderr=DEVNULL,
                                close_fds=True).wait() != 1:
                continue

            # run the nbd-client and check that returns 0
            if subprocess.Popen([self.nbd_client_binary,
                                self.server, device,
                                '-block-size', str(self.block_size),
                                '-timeout', str(self.nbd_timeout),
                                #'-persist',
                                '-name', export],
                                stdout=DEVNULL, stderr=DEVNULL,
                                close_fds=True).wait() != 0:
                continue

            # mark the device as used and return
            sysname = os.path.split(device)[1]
            subprocess.Popen([self.udevadm_binary,
                        'trigger', '--action=add',
                        '--sysname-match=%s' % sysname,
                        '--sysname-match=%sp*' % sysname],
                        stdout=DEVNULL, stderr=DEVNULL,
                        close_fds=True).wait()

            self._add(export, device)
            break

    def _do_remove(self, export):
        '''remove the export, add the device to
        the unused devices and trigger the udev rule.'''
        # remove the export
        device = self._remove(export)
        if device != None:
            # trigger the remove udev rule
            sysname = os.path.split(device)[1]
            subprocess.Popen([self.udevadm_binary,
                            'trigger', '--action=remove',
                            '--sysname-match=%sp*' % sysname,
                            '--sysname-match=%s' % sysname],
                            stdout=DEVNULL, stderr=DEVNULL,
                            close_fds=True).wait()
            # Stop the clients
            subprocess.Popen([self.nbd_client_binary, '-d', device],
                            stdout=DEVNULL, stderr=DEVNULL,
                            close_fds=True).wait()

    def _query(self):
        '''Query the remote wrapper HTTP server and get the nbd config file.
        Consider only the exports that start with the given
        mark and create two sets, the added exports and the removed exports.
        Execute the remove and add actions.'''
        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.socket.settimeout(self.poll_interval)
        try:
            self.socket.connect(self.exports_addr)
            get = HTTP_GET_SLEEP % self.poll_interval \
                if self.started else HTTP_GET_START
            self.socket.sendall(get.encode(ENCODING))
            f = self.socket.makefile('r')
            # Skip the header
            for line in f:
                if not line.strip():
                    break
            # Parse the config file
            cfg = configparser.ConfigParser()
            cfg.readfp(f)
            self.socket.close()
            self.started = True
            # Search changes in the exports
            local_exports = set(self.exports.keys())
            remote_exports = set()
            mark_len = len(EXPORT_MARK)
            for section in cfg.sections():
                if section[:mark_len] == EXPORT_MARK:
                    remote_exports.add(section)
            added = remote_exports - local_exports
            removed = local_exports - remote_exports
            for export in removed:
                self._do_remove(export)
            for export in added:
                self._do_add(export)
        except (configparser.Error, socket.error):
            # Stop everything so we fire all the connected
            # devices when the server comes up again
            self._stop_clients()
            # Wait a bit if we cannot connect
            self.error_wait.wait(ERROR_WAIT)
            self.error_wait.clear()

    def run(self):
        'Run until the unprivileged process receives the TERM signal.'
        self.stopper = Stopper(self, self.queue)
        while not self.leave:
            # Query forever
            try:
                self._query()
            except:
                self.error_wait.wait(ERROR_WAIT)
                self.error_wait.clear()
        # Stop all the nbd-clients on exit
        self._stop_clients()

class Client(object):
    '''This is the client class, it starts the privileged Server
    and after that drops privileges to be able to listen for a TERM signal
    from an unprivileged user (the user that is running the X session).
    This class only task is to stop the privileged server by using a queue
    and keep a pid file so the unprivileged user is able to send the TERM
    signal when the X session logs out.'''
    def __init__(self, server,
                 port=DEF_EXPORTS_PORT,
                 nbd_timeout=DEF_NBD_TIMEOUT,
                 nbd_client_binary=DEF_NBD_CLIENT,
                 udevadm_binary=DEF_UDEVADM,
                 poll_interval=DEF_POLL_INTERVAL,
                 block_size=DEF_BLOCK_SIZE,
                 pid_file=DEF_PID_FILE):
        self.queue = mp.Queue()
        self.pid_file = os.path.join(
            pwd.getpwuid(int(os.environ[SUDO_UID])).pw_dir,
            os.path.split(pid_file)[1])
        self.worker = Worker(self.queue,
            server, port, nbd_timeout, nbd_client_binary,
            udevadm_binary, poll_interval, block_size)
        self._drop_privileges()
        # Unprivileged after here
        self.lock = threading.Lock()
        self.lock.acquire()
        signal.signal(signal.SIGTERM, self.signal_term)
        open(self.pid_file, 'w+').write('%d\n' % os.getpid())
        self.lock.acquire()

    def _drop_privileges(self):
        'Drop user privileges to the nbbwrapper user and group'
        os.setgroups([])
        os.setgid(int(os.environ[SUDO_GID]))
        os.setuid(int(os.environ[SUDO_UID]))
        os.umask(0o077)

    def signal_term(self, signum, frame):
        '''Listen for the TERM signal and send a None on
        the worker Queue to stop it. After that we realease the lock
        and leave the program.'''
        self.queue.put(None)
        self.lock.release()
        try: os.unlink(self.pid_file)
        except OSError: pass

def install(options):
    '''Installs this software by:

        + Copying this python into /usr/local/sbin
        + Installing the UDEV rules into /etc/udev/rules.d
        + Creating a modprobe file for the nbd module options
        + Configure the autoloading of the module nbd (only on Gentoo)
        + Creating a X11 xinit file for starting the client
        + Creating the shutdown script on /usr/local/sbin
        + Linking the shutdown script in /etc/kde/shutdown
        + Linking the shutdown script in /etc/gdm/PostSession
        + Configure a sudoers file to let users on the plugdev group
          launch the nbd wrapper client (right now root is required
          to use nbd-client and udevadm)

        The only modified system files are:
            /etc/conf.d/modules - only on Gentoo to modprobe the nbd module
            /etc/X11/gdm/PostSession/Default - to call the shutdown script
    '''
    re_extension = re.compile(r'(\.[^\.]+)*$')
    re_shell = re.compile(r'^\s*(?P<shell>#!/bin/(ba)*sh)\s*$', re.M)
    udev_base = '/etc/udev/rules.d'
    base = '/usr/local/sbin'
    modprobe_d = '/etc/modprobe.d'
    xinit_rc_d = '/etc/X11/xinit/xinitrc.d'
    conf_d_modules = '/etc/conf.d/modules'
    sudoers_d = '/etc/sudoers.d'
    module_load = 'modules="$modules nbd"'
    kde_shutdown = '/etc/kde/shutdown'
    gdm_shutdown = '/etc/X11/gdm/PostSession/Default'
    gdm_comment = '# shutdown the ndb-wrapper'
    src_py = os.path.abspath(sys.argv[0])
    prog_py = os.path.split(src_py)[1]
    wrapper_py = os.path.join(base, prog_py)
    wrapper_sh = re_extension.sub('.sh', wrapper_py)
    udev_rules = os.path.join(
        udev_base, '99-%s' % re_extension.sub('.rules', prog_py))
    sudo_file = os.path.join(
        sudoers_d, '99-%s' % re_extension.sub('', prog_py))
    xinit_client = os.path.join(
        xinit_rc_d, '99-%s' % re_extension.sub('', prog_py))
    modprobe_conf = os.path.join(
        modprobe_d, re_extension.sub('.conf', prog_py))
    shutdown_sh = os.path.join(
        base, re_extension.sub('-shutdown.sh', prog_py))

    # Configure the client launcher options
    client_options = {'wrapper_py' : wrapper_py, 'wrapper_sh': wrapper_sh,
                      'plugdev' : PLUGDEV_GROUP, 'port': '', 'interval': '',
                      'block': '', 'nbd': '', 'udev': '', 'timeout': '',
                      'pid': '', 'xpid': DEF_PID_FILE}
    if options.port != DEF_EXPORTS_PORT:
        client_options['port'] = ' -p %d' % options.port
    if options.poll_interval != DEF_POLL_INTERVAL:
        client_options['interval'] = ' -i %d' % options.poll_interval
    if options.block_size != DEF_BLOCK_SIZE:
        client_options['block'] = ' -b %s' % options.block_size
    if options.nbd_timeout != DEF_NBD_TIMEOUT:
        client_options['timeout'] = ' -t %s' % options.nbd_timeout
    if options.nbd_client_binary != DEF_NBD_CLIENT:
        client_options['nbd'] = " -N '%s'" % options.nbd_client_binary
    if options.udevadm_binary != DEF_UDEVADM:
        client_options['udev'] = " -U '%s'" % options.udevadm_binary
    if options.pid_file != DEF_PID_FILE:
        xpid = os.path.split(options.pid_file)[1]
        client_options['pid'] = " -P '%s'" % xpid
        client_options['xpid'] = xpid

    if not os.path.isdir(udev_base):
        sys.stderr.write(
            'ERROR: The UDEV rules directory %s does not exist.\n'
            'Is UDEV installed on this system?\n' % udev_base)
        return 10

    if not os.path.exists(options.nbd_client_binary):
        sys.stderr.write(
            'ERROR: The binary file %s does not exist.\n'
            'Please, specify the option --nbd-client-binary '
            'pointing to the nbd client binary.\n')
        return 11

    if not os.path.exists(options.udevadm_binary):
        sys.stderr.write(
            'ERROR: The binary file %s does not exist.\n'
            'Please, specify the option --udevadm-binary '
            'pointing to the udevadm binary.\n')
        return 12

    # Install the client wrapper
    try: os.makedirs(base, 755)
    except OSError: pass
    if os.path.isdir(base):
        try:
            f = open(src_py, 'r')
            data = f.read()
            f.close()
            f = open(wrapper_py, 'w')
            os.fchown(f.fileno(), 0, 0)
            os.fchmod(f.fileno(), 0o500)
            f.write(data)
            f.close()
            print('file %s ready.' % wrapper_py)
        except (OSError, IOError):
            sys.stderr.write(
                'ERROR: Cannot write the file %s, '
                'you should run the installer as root.\n' % wrapper_py)
            return 13
        try:
            f = open(wrapper_sh, 'w')
            os.fchown(f.fileno(), 0, 0)
            os.fchmod(f.fileno(), 0o500)
            f.write(SAFE_SHELL % client_options)
            f.close()
            print('file %s ready.' % wrapper_sh)
        except (OSError, IOError):
            sys.stderr.write(
                'ERROR: Cannot write the file %s, '
                'you should run the installer as root.\n' % wrapper_sh)
            return 13
    else:
        sys.stderr.write(
            'ERROR: Cannot find the directory %s, '
            'you should run the installer as root.\n' % base)
        return 13

    # Install the UDEV rules
    try:
        f = open(udev_rules, 'w')
        os.fchown(f.fileno(), 0, 0)
        os.fchmod(f.fileno(), 0o644)
        f.write(UDEV_RULES)
        f.close()
        os.system('udevadm control --reload')
        print('file %s ready.' % udev_rules)
    except (OSError, IOError):
        sys.stderr.write(
            'ERROR: Cannot write the file %s, '
            'you should run the installer as root.\n' % udev_rules)
        return 14

    # Create a modprobe file for the nbd options
    if os.path.isdir(modprobe_d):
        try:
            f = open(modprobe_conf, 'w')
            os.fchown(f.fileno(), 0, 0)
            os.fchmod(f.fileno(), 0o644)
            f.write('options nbd max_part=63\n')
            f.close()
            os.system('modprobe nbd')
            print('file %s ready.' % modprobe_conf)
        except (OSError, IOError):
            sys.stderr.write(
                'ERROR: Cannot write the file %s, '
                'you should run the installer as root.\n' % modprobe_conf)
            return 15
    else:
        sys.stderr.write(
            'WARNING: Cannot find the %s directory, manually configure '
            'your distro to do a "modprobe nbd '
            'max_part=63" on boot.\n' % modprobe_d)

    # Try to autoload the module on boot (only on Gentoo)
    if os.path.isfile(conf_d_modules):
        try:
            f = open(conf_d_modules, 'r')
            data = f.read()
            f.close()
            if data.find(module_load) == -1:
                f = open(conf_d_modules, 'a')
                f.write('\n%s\n' % module_load)
                f.close()
                print('file %s ready.' % conf_d_modules)
            else:
                print('file %s already configured.' % conf_d_modules)
        except (OSError, IOError):
            sys.stderr.write(
                'ERROR: Cannot write %s, '
                'you should run the installer as root.\n' % conf_d_modules)
            return 16
    else:
        sys.stderr.write(
            'WARNING: Cannot find the %s file, manually configure '
            'your distro to do a "modprobe nbd" on boot.\n' % conf_d_modules)

    # Create a xinit script to start the nbd wrapper client
    # on every X session that requires it (ie: a remote session)
    if os.path.isdir(xinit_rc_d):
        try:
            f = open(xinit_client, 'w')
            os.fchown(f.fileno(), 0, 0)
            os.fchmod(f.fileno(), 0o755)
            f.write(XINIT_CLIENT % client_options)
            f.close()
            print('file %s ready.' % xinit_client)
        except (OSError, IOError):
            sys.stderr.write(
                'ERROR: Cannot write the file %s, '
                'you should run the installer as root.\n' % xinit_client)
            return 17
    else:
        sys.stderr.write(
            'WARNING: Cannot find the %s directory, manually create '
            'a xinit file with this content:\n' % xinit_rc_d)
        sys.stderr.write(XINIT_CLIENT % client_options)

    # Create the shutdown script
    try:
        f = open(shutdown_sh, 'w')
        os.fchown(f.fileno(), 0, 0)
        os.fchmod(f.fileno(), 0o755)
        f.write(SHUTDOWN_SHELL % client_options)
        f.close()
        print('file %s ready.' % shutdown_sh)
    except (OSError, IOError):
        sys.stderr.write(
            'ERROR: Cannot write the file %s, '
            'you should run the installer as root.\n' % shutdown_sh)
        return 18

    # Link the shutdown script on /etc/kde/shutdown
    kde_shutdown_link = os.path.join(
        kde_shutdown, os.path.split(shutdown_sh)[1])
    if os.path.isdir(kde_shutdown):
        try:
            os.link(shutdown_sh, kde_shutdown_link)
            print('link %s ready.' % kde_shutdown_link)
        except OSError:
            print('link %s already done.' % kde_shutdown_link)
    else:
        sys.stderr.write(
            'WARNING: Cannot find the %s directory, manually link '
            'the %s script in the KDE shutdown directory.\n' % (
                kde_shutdown, shutdown_sh))

    # Link the shutdown script on /etc/X11/gdm/PostSession
    if os.path.isfile(gdm_shutdown):
        try:
            f = open(gdm_shutdown, 'r')
            data = f.read()
            f.close()
            if data.find(gdm_comment) == -1:
                f = open(gdm_shutdown, 'w')
                os.fchown(f.fileno(), 0, 0)
                os.fchmod(f.fileno(), 0o755)
                f.write(re_shell.sub(
                    lambda m: '%s\n\n%s\n%s\n' % (
                        m.group('shell'), gdm_comment, shutdown_sh), data))
                f.close()
                print('file %s ready.' % gdm_shutdown)
            else:
                print('file %s already done.' % gdm_shutdown)
        except (OSError, IOError):
            sys.stderr.write(
                'ERROR: Cannot write the file %s, '
                'you should run the installer as root.\n' % gdm_shutdown)
            return 13
    else:
        sys.stderr.write(
            'WARNING: Cannot find the %s directory, manually add '
            'the %s script to the GDM PostSession/Default script.\n' % (
                gdm_shutdown, shutdown_sh))

    # Create a modprobe file for the nbd options
    if os.path.isdir(sudoers_d):
        try:
            f = open(sudo_file, 'w')
            os.fchown(f.fileno(), 0, 0)
            os.fchmod(f.fileno(), 0o440)
            f.write(SUDOERS_LINE % client_options)
            f.close()
            os.system("VISUAL=/usr/bin/touch visudo -f '%s'" % sudo_file)
            print('file %s ready.' % sudo_file)
        except (OSError, IOError):
            sys.stderr.write(
                'ERROR: Cannot write the file %s, '
                'you should run the installer as root.\n' % sudo_file)
            return 19
    else:
        sys.stderr.write(
            'WARNING: Cannot find the %s directory, manually '
            'add this line to the /etc/sudoers file:\n' % sudoers_d)
        sys.stderr.write(SUDOERS_LINE % client_options)

    print('''
You can add these lines to the syslog-ng.conf file just under the
"source src {...}" section because the nbd-server could get very verbose:

 destination discard { file("/dev/null" owner(root) group(root) perm(0666) dir_perm(0755) create_dirs(no)); };
 filter nbd { program("nbd_server"); };
 log { source(src); filter(nbd); destination(discard); flags(final); };
''')

    return 0

def main():
    parser = optparse.OptionParser(description='''\
%prog: handles remote media using nbd-client processes.
Copyright (C) 2014  Juan Carlos Rodrigo
This program comes with ABSOLUTELY NO WARRANTY.
This is free software, and you are welcome to redistribute it
under certain conditions.''', version='%%prog %s' % __version__)
    parser.add_option('-s', '--server', dest='server', action='store',
                        default=None, help='nbd-wrapper server to query')
    parser.add_option('-p', '--exports-port', dest='port',
                        action='store', default=DEF_EXPORTS_PORT,
                        help='the nbd-wrapper server port')
    parser.add_option('-i', '--poll-interval', dest='poll_interval',
                        type='int', default=DEF_POLL_INTERVAL,
                        help='query interval in seconds')
    parser.add_option('-b', '--block-size', dest='block_size',
                        choices=DEF_BLOCK_SIZES, default=DEF_BLOCK_SIZE,
                        help='nbd-client block size')
    parser.add_option('-t', '--nbd-timeout', dest='nbd_timeout',
                        type='int', default=DEF_NBD_TIMEOUT,
                        help='nbd-client timeout connecting')
    parser.add_option('-N', '--nbd-client-binary', dest='nbd_client_binary',
                        action='store', default=DEF_NBD_CLIENT,
                        help='the nbd-client binary file')
    parser.add_option('-U', '--udevadm-binary', dest='udevadm_binary',
                        action='store', default=DEF_UDEVADM,
                        help='the udevadm binary file')
    parser.add_option('-P', '--pid-file', dest='pid_file',
                        action='store', default=DEF_PID_FILE,
                        help='the pid file name (always under $HOME)')
    parser.add_option('-I', '--install', dest='install', action='store_true',
                        default=False,
                        help='installs this software')
    (options, args) = parser.parse_args()

    ret = 0
    if options.server != None:
        worker = Client(options.server, options.port, options.nbd_timeout,
                        options.nbd_client_binary, options.udevadm_binary,
                        options.poll_interval, options.block_size,
                        options.pid_file)
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
