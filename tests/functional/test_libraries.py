#-----------------------------------------------------------------------------
# Copyright (c) 2005-2023, PyInstaller Development Team.
#
# Distributed under the terms of the GNU General Public License (version 2
# or later) with exception for distributing the bootloader.
#
# The full license is in the file COPYING.txt, distributed with this software.
#
# SPDX-License-Identifier: (GPL-2.0-or-later WITH Bootloader-exception)
#-----------------------------------------------------------------------------

import pathlib

import pytest

from PyInstaller import compat
from PyInstaller.utils.tests import importable, importorskip, onedir_only, parametrize, requires, skipif
from PyInstaller.utils.hooks import can_import_module, tcl_tk


@importorskip('gevent')
def test_gevent(pyi_builder):
    pyi_builder.test_source("""
        import gevent
        gevent.spawn(lambda: x)
        """)


@importorskip('gevent')
def test_gevent_monkey(pyi_builder):
    pyi_builder.test_source("""
        from gevent.monkey import patch_all
        patch_all()
        """)


@importorskip('IPython')
def test_ipython(pyi_builder, capfd):
    pyi_builder.test_source(
        """
        import os
        import sys

        # Redirect sys.stdin to devnull to force IPython console to automatically exit
        with open(os.devnull, 'r') as sys.stdin:
            import IPython
            print("Calling IPython.embed()...", file=sys.stderr)
            IPython.embed(header="Hello from embedded IPython!")
            print("End of program reached!", file=sys.stderr)
        """
    )

    out, err = capfd.readouterr()
    assert 'Hello from embedded IPython!' in out, \
        f"Cannot find hello string in captured output:\n{out}"


# The tkinter module may be available for import, but not actually importable due to missing shared libraries.
# Therefore, we need to use `can_import_module`-based skip decorator instead of `@importorskip`.
@pytest.mark.skipif(not can_import_module("tkinter"), reason="tkinter cannot be imported.")
def test_tkinter_tcl_library_dir(pyi_builder):
    pyi_builder.test_source(
        """
        import sys
        import pathlib
        import tkinter

        # Query the location of Tcl library/data directory.
        tcl = tkinter.Tcl()
        tcl_data_dir = tcl.eval("info library")

        print(f"Tcl directory: {tcl_data_dir}", file=sys.stderr)

        if tcl_data_dir == "//zipfs:/lib/tcl/tcl_library":
            # Tcl/Tk 9 with data embedded in shared library
            print("Tcl data is embedded in shared library!", file=sys.stderr)
        elif (
            sys.platform == 'darwin' and
            tcl_data_dir == "/System/Library/Frameworks/Tcl.framework/Versions/8.5/Resources/Scripts"
        ):
            # macOS python build with system Tcl/Tk .framework
            print("System Tcl/Tk .framework on macOS", file=sys.stderr)
        else:
            # Check that Tcl data directory is collected in frozen application
            application_dir = pathlib.Path(sys._MEIPASS).resolve()
            tcl_data_dir = pathlib.Path(tcl_data_dir).resolve()

            if application_dir not in tcl_data_dir.parents:
                raise SystemExit(
                    f"Tcl data directory {str(tcl_data_dir)!r} is not located inside {str(application_dir)!r}"
                )
        """
    )


# In contrast to test_tkinter_tcl_library_dir, which performs basic import test and verifies that the path to Tcl
# library directory is set properly, this is a full functional test; we try to create a Tk window with label and
# button, and register a timer to shut down the application. Doing so verifies that all Tcl/Tk files (e.g., .tcl
# scripts from library directories) are properly collected.
#
# The prerequisite for this test is that tkinter can be used unfrozen, so check that this is indeed the case.
def test_tkinter_functional(pyi_builder):
    if not tcl_tk.tcltk_info.tkinter_fully_usable:
        pytest.skip("tkinter is not fully usable.")

    pyi_builder.test_source(
        """
        import tkinter
        import tkinter.messagebox

        root = tkinter.Tk()

        # Dump information about library/data directory.
        tcl_dir = root.tk.exprstring('$tcl_library')
        print(f"Run-time Tcl library/data directory: {tcl_dir}")

        tk_dir = root.tk.exprstring('$tk_library')
        print(f"Run-time Tk library/data directory: {tk_dir}")

        # Create test GUI
        label = tkinter.Label(root, text="Hello World")
        label.pack()

        def test_button_callback():
            tkinter.messagebox.showinfo("Test", "Test message")

        button = tkinter.Button(root, text="Test button", command=test_button_callback)
        button.pack()

        def shutdown_timer_callback():
            print("Shutting down!")
            root.destroy()

        shutdown_interval = 1000  # ms
        print(f"Starting shutdown timer ({shutdown_interval} ms)...")
        root.after(shutdown_interval, shutdown_timer_callback)

        print("Entering main loop...")
        root.mainloop()

        print("Done!")
    """
    )


@importorskip('sphinx')
def test_sphinx(pyi_builder, data_dir):
    pyi_builder.test_script(
        'pyi_lib_sphinx.py',
        # Pass the path to temporary copy of data directory via command-line arguments.
        app_args=[str(data_dir)],
    )


@importorskip('pygments')
def test_pygments(pyi_builder):
    pyi_builder.test_source(
        """
        # This sample code is taken from http://pygments.org/docs/quickstart/.
        from pygments import highlight
        from pygments.lexers import PythonLexer
        from pygments.formatters import HtmlFormatter

        code = 'print "Hello World"'
        print(highlight(code, PythonLexer(), HtmlFormatter()))
        """
    )


@requires('zope.interface')
def test_zope_interface(pyi_builder):
    # Tests that `nspkg.pth`-based namespace package are bundled properly. The `nspkg.pth` file is created by
    # setuptools and thus changes frequently. If this test fails, most probably _SETUPTOOLS_NAMESPACEPKG_PTHs
    # in modulegraph needs to be updated.
    pyi_builder.test_source(
        """
        # Package 'zope' does not contain __init__.py file.
        # Just importing 'zope.interface' is sufficient.
        import zope.interface
        """
    )


# The tkinter module may be available for import, but not actually importable due to missing shared libraries.
# Therefore, we need to use `can_import_module`-based skip decorator instead of `@importorskip`.
@importorskip('idlelib')
@pytest.mark.skipif(not can_import_module("tkinter"), reason="tkinter cannot be imported.")
def test_idlelib(pyi_builder):
    pyi_builder.test_source(
        """
        # This file depends on loading some icons, located based on __file__.
        import idlelib.tree
        """
    )


@importorskip('keyring')
@skipif(
    compat.is_linux,
    reason="SecretStorage backend on linux requires active D-BUS session and initialized keyring, and may "
    "need to unlock the keyring via UI prompt."
)
def test_keyring(pyi_builder):
    pyi_builder.test_source("""
        import keyring
        keyring.get_password("test", "test")
        """)


@importorskip('numpy')
def test_numpy(pyi_builder):
    pyi_builder.test_source(
        """
        import numpy
        from numpy.core.numeric import dot
        print('dot(3, 4):', dot(3, 4))
        """
    )


@importorskip('pytz')
def test_pytz(pyi_builder):
    pyi_builder.test_source("""
        import pytz
        pytz.timezone('US/Eastern')
        """)


@importorskip('requests')
@skipif(
    compat.is_cygwin,
    reason="ssl server is broken on cygwin until https://github.com/python/cpython/pull/150419 is released/back-ported."
)
def test_requests(pyi_builder, data_dir):
    # NOTE: including the `data_dir` fixture copies files needed by this test!
    # We collect the data into frozen application.
    add_data_arg = f"{data_dir / '*'}:."
    pyi_builder.test_script('pyi_lib_requests.py', pyi_args=['--add-data', add_data_arg])


@importorskip('sqlite3')
def test_sqlite3(pyi_builder):
    pyi_builder.test_source(
        """
        # PyInstaller did not included module 'sqlite3.dump'.
        import sqlite3
        conn = sqlite3.connect(':memory:')
        csr = conn.cursor()
        csr.execute('CREATE TABLE Example (id)')
        for line in conn.iterdump():
             print(line)
        """
    )


@requires('scapy >= 2.0')
def test_scapy(pyi_builder):
    pyi_builder.test_source(
        """
        # Test-cases taken from issue #834
        import scapy.all
        scapy.all.IP

        from scapy.all import IP

        # Test-case taken from issue #202.
        from scapy.all import *
        DHCP  # scapy.layers.dhcp.DHCP
        BOOTP  # scapy.layers.dhcp.BOOTP
        DNS  # scapy.layers.dns.DNS
        ICMP  # scapy.layers.inet.ICMP
        """
    )


@requires('scapy >= 2.0')
def test_scapy2(pyi_builder):
    pyi_builder.test_source(
        """
        # Test the hook to scapy.layers.all
        from scapy.layers.all import DHCP
        """
    )


@requires('scapy >= 2.0')
def test_scapy3(pyi_builder):
    pyi_builder.test_source(
        """
        # Test whether
        # a) scapy packet layers are not included if neither scapy.all nor scapy.layers.all are imported
        # b) packages are included if imported explicitly

        NAME = 'hook-scapy.layers.all'
        layer_inet = 'scapy.layers.inet'

        def testit():
            try:
                __import__(layer_inet)
                raise SystemExit('Self-test of hook %s failed: package module found'
                                 % NAME)
            except ImportError as e:
                if not e.args[0].endswith(' inet'):
                    raise SystemExit('Self-test of hook %s failed: package module found and has import errors: %r'
                                     % (NAME, e))

        import scapy
        testit()
        import scapy.layers
        testit()
        # Explicitly import a single layer module. Note: This module MUST NOT import inet (neither directly nor
        # indirectly), otherwise the test above fails.
        import scapy.layers.ir
        """
    )


@importorskip('sqlalchemy')
def test_sqlalchemy(pyi_builder):
    pyi_builder.test_source(
        """
        # The hook behaviour is to include with sqlalchemy all installed database backends.
        import sqlalchemy
        # This import was known to fail with sqlalchemy 0.9.1
        import sqlalchemy.ext.declarative
        """
    )


@importorskip('twisted')
def test_twisted(pyi_builder):
    pyi_builder.test_source(
        """
        # Twisted is an event-driven networking engine.
        #
        # The 'reactor' is object that starts the eventloop.
        # There are different types of platform specific reactors.
        # Platform specific reactor is wrapped into twisted.internet.reactor module.
        from twisted.internet import reactor
        # Applications importing module twisted.internet.reactor might fail with error like:
        #
        #     AttributeError: 'module' object has no attribute 'listenTCP'
        #
        # Ensure default reactor was loaded - it has method 'listenTCP' to start server.
        if not hasattr(reactor, 'listenTCP'):
            raise SystemExit('Twisted reactor not properly initialized.')
        """
    )


@importorskip('usb')
@pytest.mark.skipif(compat.is_linux, reason='libusb_exit segfaults on some linuxes')
def test_usb(pyi_builder):
    # See if the usb package is supported on this platform.
    try:
        import usb
        # This will verify that the backend is present; if not, it will skip this test.
        usb.core.find()
    except (ImportError, usb.core.NoBackendError):
        pytest.skip('USB backnd not found.')

    pyi_builder.test_source(
        """
        import usb.core
        # NoBackendError fails the test if no backends are found.
        usb.core.find()
        """
    )


@importorskip('zeep')
def test_zeep(pyi_builder):
    pyi_builder.test_source(
        """
        # Test the hook to zeep
        from zeep import utils
        utils.get_version()
        """
    )


@importorskip('pandas')
def test_pandas_extension(pyi_builder):
    # Tests that the C extension ``pandas._libs.lib`` is properly bundled. Issue #1580.
    # See http://pandas.pydata.org/pandas-docs/stable/whatsnew.html#modules-privacy-has-changed.
    pyi_builder.test_source(
        """
        from pandas._libs.lib import is_float
        assert is_float(1) == 0
        """
    )


@importorskip('pandas')
@importorskip('jinja2')
def test_pandas_io_formats_style(pyi_builder):
    # pandas.io.formats.style requires jinja2 as hiddenimport, as well as collected template file
    # from pandas/io/formats/templates. See #6008 and #6009.
    pyi_builder.test_source("""
        import pandas.io.formats.style
        """)


@importorskip('pandas')
@importorskip('matplotlib')
def test_pandas_plotting_matplotlib(pyi_builder):
    # Test that pandas.plotting works. Starting with pandas 1.3.0, the used pandas.plotting._matplotlib backend module
    # is loaded via importlib.import_module(), and needs a hidden import. See #5994.
    pyi_builder.test_source(
        """
        import matplotlib as mpl
        import pandas as pd

        mpl.use('Agg')  # Use headless Agg backend to avoid dependency on display server.

        series = pd.Series([0, 1, 2, 3], [0, 1, 2, 3])
        series.plot()
        """
    )


@importorskip('win32ctypes')
@pytest.mark.skipif(not compat.is_win, reason='pywin32-ctypes is supported only on Windows')
@pytest.mark.parametrize('submodule', ['win32api', 'win32cred', 'pywintypes'])
def test_pywin32ctypes(pyi_builder, submodule):
    pyi_builder.test_source(f"""
        from win32ctypes.pywin32 import {submodule}
        """)


@importorskip('setuptools')
def test_setuptools(pyi_builder):
    pyi_builder.test_source("""
        import setuptools
        """)


@importorskip('babel')
def test_babel(pyi_builder):
    # Try to format a date/time in order to ensure that data files from babel's locale-data directory (especially
    # root.dat) can be unpickled.
    pyi_builder.test_source(
        """
        import datetime
        from babel.dates import format_datetime

        datetime_obj = datetime.datetime(2007, 4, 1, 15, 30)
        print(format_datetime(datetime_obj, 'full', locale='fr_FR'))
        """
    )


# ---------------------------------------------------------------------------
# Pillow (PIL)
# ---------------------------------------------------------------------------

# Functional test that tries to convert a .tiff image to a .png
@importorskip('PIL')
def test_pil_image_conversion(pyi_builder, tmp_path):
    pyi_builder.test_source(
        """
        import sys
        import os

        import PIL.Image

        if len(sys.argv) != 3:
            print(f"use: {sys.argv[0]} <input-filename> <output-filename>")
            raise SystemExit(1)

        input_file = sys.argv[1]
        output_file = sys.argv[2]

        image = PIL.Image.open(input_file)
        image.save(output_file)
        """,
        app_args=[
            str(pathlib.Path(__file__).parent / 'data' / 'PIL_images' / 'tinysample.tiff'),
            str(tmp_path / 'converted_tinysample.png'),
        ],
    )


@importorskip('PIL')
@importorskip('PyQt5')
def test_pil_pyqt5(pyi_builder):
    # hook-PIL is excluding PyQt5, but is must still be included since it is imported elsewhere.
    # Also see issue #1584.
    pyi_builder.test_source("""
        import PyQt5
        import PIL
        import PIL.ImageQt
        """)


@importorskip('PIL')
def test_pil_plugins(pyi_builder):
    pyi_builder.test_source(
        """
        # Verify packaging of PIL.Image.
        from PIL.Image import frombytes
        print(frombytes)

        # PIL import hook should bundle all available PIL plugins. Verify that plugins are collected.
        from PIL import Image
        Image.init()
        MIN_PLUG_COUNT = 7  # Without all plugins the count is usually 6.
        plugins = list(Image.SAVE.keys())
        plugins.sort()
        if len(plugins) < MIN_PLUG_COUNT:
            raise SystemExit('No PIL image plugins were collected!')
        else:
            print('PIL supported image formats: %s' % plugins)
        """
    )


# The tkinter module may be available for import, but not actually importable due to missing shared libraries.
# Therefore, we need to use `can_import_module`-based skip decorator instead of `@importorskip`.
@pytest.mark.skipif(not can_import_module("tkinter"), reason="tkinter cannot be imported.")
@importorskip('PIL')
def test_pil_no_tkinter(pyi_builder):
    """
    Ensure that the Tkinter package excluded by `PIL` package hooks is unimportable by frozen applications explicitly
    importing only the latter.
    """

    pyi_builder.test_source(
        """
        import PIL.Image

        # Dynamically importing the Tkinter package should fail with an "ImportError", implying "PIL" package hooks
        # successfully excluded Tkinter. To prevent PyInstaller from parsing this import and thus freezing this
        # extension with this test, this import is dynamic.
        try:
            __import__('tkinter')
            raise SystemExit('ERROR: Module tkinter is bundled.')
        except ImportError:
            pass

        # Dynamically importing the "_tkinter" shared library should also fail.
        try:
            __import__('_tkinter')
            raise SystemExit('ERROR: Module _tkinter is bundled.')
        except ImportError:
            pass
        """
    )


# The tkinter module may be available for import, but not actually importable due to missing shared libraries.
# Therefore, we need to use `can_import_module`-based skip decorator instead of `@importorskip`.
@pytest.mark.skipif(not can_import_module("tkinter"), reason="tkinter cannot be imported.")
@importorskip('PIL')
def test_pil_tkinter(pyi_builder):
    """
    Ensure that the Tkinter package excluded by `PIL` package hooks is importable by frozen applications explicitly
    importing both.

    == See Also ==

    * PyInstaller [issue #1584](https://github.com/pyinstaller/pyinstaller/issues/1584).
    """

    pyi_builder.test_source(
        """
        import PIL.Image

        # Statically importing the Tkinter package should succeed, implying this importation successfully overrode
        # the exclusion of this package requested by "PIL" package hooks. To ensure PyInstaller parses this import
        # and freezes this package with this test, this import is static.
        try:
            import tkinter
        except ImportError:
            raise SystemExit('ERROR: Module tkinter is NOT bundled.')
        """
    )


@importorskip('PIL')
@importorskip('matplotlib')
def test_pil_no_matplotlib(pyi_builder):
    """
    Ensure that using PIL.Image does not pull in `matplotlib` when the latter is not explicitly imported by the program.
    The import chain in question,
    PIL.Image -> PIL -> PIL.ImageShow -> IPython -> matplotlib_inline.backend_inline -> matplotlib,
    should be broken by the PIL hook excluding IPython.
    """

    pyi_builder.test_source(
        """
        import PIL.Image

        # Use dynamic import of matplotlib to prevent PyInstaller from picking up the import.
        try:
            __import__('matplotlib')
            raise SystemExit('ERROR: matplotlib is bundled.')
        except ImportError:
            pass
        """
    )


# ---------------------------------------------------------------------------
# SciPy
# ---------------------------------------------------------------------------

# Basic import test for each scipy module, to ensure that each module is importable on its own. Due to amount of tests,
# run them only in onedir mode.
@importorskip('scipy')
@pytest.mark.parametrize(
    'module', [
        'scipy',
        'scipy.cluster',
        'scipy.constants',
        'scipy.datasets',
        'scipy.differentiate',
        'scipy.fft',
        'scipy.fftpack',
        'scipy.integrate',
        'scipy.interpolate',
        'scipy.io',
        'scipy.linalg',
        'scipy.misc',
        'scipy.ndimage',
        'scipy.odr',
        'scipy.optimize',
        'scipy.signal',
        'scipy.sparse',
        'scipy.spatial',
        'scipy.special',
        'scipy.stats',
    ]
)
@onedir_only
def test_scipy(pyi_builder, module):
    if not importable(module):
        pytest.skip(f"Can't import {module!r}.")
    pyi_builder.test_source(f"""
        import {module}
        """)


# ---------------------------------------------------------------------------
# PyGObject
# ---------------------------------------------------------------------------

# Names of all "gi.repository" packages provided by PyGObject  to be tested below, typically corresponding to
# those packages hooked by PyInstaller.
_gi_repositories = [
    ('Gst', '1.0'),
    ('GLib', '2.0'),
    ('GModule', '2.0'),
    ('GObject', '2.0'),
    ('GdkPixbuf', '2.0'),
    ('Gio', '2.0'),
    ('Clutter', '1.0'),
    ('GtkClutter', '1.0'),
    ('Champlain', '0.12'),
    ('GtkChamplain', '0.12'),
]


# Test the usability of "gi.repository" packages provided by PyGObject.
@importorskip('gi.repository')
@parametrize(
    ('repository_name', 'version'),
    [pytest.param(name, version, marks=importorskip(f'gi.repository.{name}')) for name, version in _gi_repositories],
    ids=[name for name, version in _gi_repositories],  # Ensure human-readable test parameter names.
)
def test_gi_repository(pyi_builder, repository_name, version):
    """
    Test the importability of the `gi.repository` subpackage with the passed name installed with PyGObject. For example,
    `GLib`, corresponds to the `gi.repository.GLib` subpackage. Version '1.0' are for PyGObject >=1.0,
    '2.0' for PyGObject >= 2.0. Some other libraries have strange version (e.g., Champlain).
    """

    # Test the importability of this subpackage.
    pyi_builder.test_source(
        f"""
        import sys
        import pathlib

        import gi

        # Check that package/namespace can be imported
        print("Importing module...", file=sys.stderr)
        gi.require_version('{repository_name}', '{version}')
        from gi.repository import {repository_name}
        print(f"  Imported: {{{repository_name}}}", file=sys.stderr)

        # Check that the typelib is, in fact, loaded from the frozen application (instead of falling back to the copy
        # that is installed on the system).
        print("Checking that module's typelib is loaded from frozen application...", file=sys.stderr)
        repo = gi.Repository.get_default()
        typelib_path = repo.get_typelib_path('{repository_name}')
        print(f"  Typelib path: {{typelib_path}}", file=sys.stderr)

        typelib_path = pathlib.Path(typelib_path).resolve()
        application_path = pathlib.Path(sys._MEIPASS).resolve()
        if application_path not in typelib_path.parents:
            raise ValueError(f"Typelib {{str(typelib_path)!r}} is not loaded from frozen application's directory!")

        # Similarly, ensure that all gi.repository sub-modules that are now registered in sys.modules (i.e., were loaded
        # during the above import of the target module) are also loaded from the frozen application. This aims to catch
        # implicit dependencies that were missed during collection, and are therefore loaded from the system.
        print("Checking all loaded gi.repository sub-modules...", file=sys.stderr)
        for module_name, module in sys.modules.items():
            if not module_name.startswith('gi.repository.'):
                continue
            module_path = module.__path__[0]
            module_path = pathlib.Path(module_path).resolve()
            print(f"  Module: {{module_name!r}}, path: {{module_path!r}}", file=sys.stderr)

            if application_path not in module_path.parents:
                raise ValueError(f"Typelib {{str(module_path)!r}} is not loaded from frozen application's directory!")
        """
    )


# GST_PLUGIN_PATH must point at the directory where the gi.repository.Gst hook puts the plugins.
@importorskip('gi.repository.Gst')
def test_gi_gst_plugin_path(pyi_builder):
    pyi_builder.test_source(
        """
        import os
        import sys

        import gi
        gi.require_version('Gst', '1.0')
        from gi.repository import Gst

        search_paths = os.environ['GST_PLUGIN_PATH'].split(os.pathsep)
        print(f"GST_PLUGIN_PATH entries: {search_paths}", file=sys.stderr)

        plugin_dir = os.path.join(sys._MEIPASS, 'gst_plugins')
        if plugin_dir not in search_paths:
            raise ValueError(f"Plugin directory {plugin_dir!r} is not in GST_PLUGIN_PATH: {search_paths}")

        missing = [path for path in search_paths if not os.path.isdir(path)]
        if missing:
            raise ValueError(f"GST_PLUGIN_PATH contains non-existent directories: {missing}")
        """
    )


# ---------------------------------------------------------------------------
# pywin32
# ---------------------------------------------------------------------------

# pywin32 provides several modules that can be imported on their own, such as win32api or win32com.
# They are located in three directories, which are added to search path via pywin32.pth:
# - win32
# - win32/lib
# - pythonwin
@importorskip('win32api')  # Use win32api to check for presence of pywin32.
@pytest.mark.parametrize(
    'module',
    (
        # Binary extensions from win32
        'mmapfile',
        'odbc',
        'perfmon',
        'servicemanager',
        'timer',
        'win32api',
        'win32clipboard',
        'win32console',
        'win32cred',
        'win32crypt',
        'win32event',
        'win32evtlog',
        'win32file',
        'win32gui',
        'win32help',
        'win32inet',
        'win32job',
        'win32lz',
        'win32net',
        'win32pdh',
        'win32pipe',
        'win32print',
        'win32process',
        'win32profile',
        'win32ras',
        'win32security',
        'win32service',
        '_win32sysloader',
        'win32trace',
        'win32transaction',
        'win32ts',
        'win32wnet',
        '_winxptheme',
        # Python modules from win32/lib
        'afxres',
        'commctrl',
        'dbi',
        'mmsystem',
        'netbios',
        'ntsecuritycon',
        'pywin32_bootstrap',
        'pywin32_testutil',
        'pywintypes',
        'rasutil',
        'regcheck',
        'regutil',
        'sspicon',
        'sspi',
        'win2kras',
        'win32con',
        'win32cryptcon',
        'win32evtlogutil',
        'win32gui_struct',
        'win32inetcon',
        'win32netcon',
        'win32pdhquery',
        'win32pdhutil',
        'win32rcparser',
        'win32serviceutil',
        'win32timezone',
        'win32traceutil',
        'win32verstamp',
        'winerror',
        'winioctlcon',
        'winnt',
        'winperf',
        'winxptheme',
        # Binary extensions from pythonwin
        'dde',
        'win32uiole',
        'win32ui',
        # Python package from pythonwin
        'pywin',
        # Packages/modules in top-level directory
        'adodbapi',
        'isapi',
        'win32com',
        'win32comext',
        'pythoncom',
    )
)
@onedir_only
def test_pywin32_imports(pyi_builder, module):
    if not can_import_module(module):
        pytest.skip(f"Module '{module}' cannot be imported.")

    # Basic import test
    pyi_builder.test_source(f"""
        import {module}
        """)


@importorskip('win32com')
def test_pywin32_win32com(pyi_builder):
    pyi_builder.test_source(
        """
        # Test importing some modules from pywin32 package.
        # All modules from pywin32 depens on module pywintypes.
        # This module should be also included.
        import win32com
        import win32com.client
        import win32com.server
        """
    )


@importorskip('win32com')
def test_pywin32_comext(pyi_builder):
    pyi_builder.test_source(
        """
        # Test importing modules from win32com that are actually present in
        # win32comext, and made available by __path__ changes in win32com.
        from win32com.shell import shell
        from win32com.propsys import propsys
        from win32com.bits import bits
        """
    )


@importorskip('win32ui')
def test_pywin32_win32ui(pyi_builder):
    pyi_builder.test_source(
        """
        # Test importing some modules from pywin32 package.
        # All modules from pywin32 depens on module pywintypes.
        # This module should be also included.
        import win32ui
        from pywin.mfc.dialog import Dialog
        d = Dialog(win32ui.IDD_SIMPLE_INPUT)
        """
    )


# ---------------------------------------------------------------------------
# Django
# ---------------------------------------------------------------------------

@importorskip('django')
def test_django(pyi_builder, monkeypatch, data_dir):
    # Extend sys.path so PyInstaller could find modules from 'tmpdir/django/'.
    monkeypatch.syspath_prepend(str(data_dir))
    # Django uses manage.py as the main script.
    script = data_dir / 'manage.py'
    # Create the exe, run django command 'check' to do basic sanity checking of the executable.
    pyi_builder.test_script(script, app_name='django_site', app_args=['check'])
