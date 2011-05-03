#!/usr/bin/env python

# obf.py:  A python-based parser for Open Behavioral [data] Format (OBF).
# Copyright 2011 by Jeremy R. Gray, jrgray@gmail.com
# Distributed under the terms of the GNU General Public License (GPL).

# Note that OBF is a separate logical entity from code that implements a parser
# or emitter


__version__ = '0.4.00' # of the parser, not OBF

import yaml
import copy
import re
import time

import StringIO # for tests


# OBF Constants:
# Special section keys, case-sensitive:
_HEADER = '=Header='
_SESSION = '=Session='
_SUBJECT = '=Subject='
_PARTICIPANT = '=Participant='
_COMMENT = '=Comment='
_NOTES = '=Notes='
_FOOTER = '=Footer='
_SPECIAL = [_HEADER, _SESSION, _SUBJECT, _PARTICIPANT, _COMMENT, _NOTES, _FOOTER]

# Parser directives: Not case-sensitive but must be lower case here, no whitespace:
_ONE_INDEXED = 'one_indexed' # first list element is referenced by [1]
_ZERO_INDEXED = 'zero_indexed' # first list element is referenced by [0]
_AUTO_INDEX = 'auto_index' # add integer labels to redundant keys
_STRICT = 'strict' # disallow (generate error, nullify data)
_WARN = 'warn' # permissive (generate a warning)
_NOT_STRICT = 'not_strict' # permissive
_KEYS_LOWER = 'keys_lower' # convert keys to all upper-case
_KEYS_UPPER = 'keys_upper' # convert keys to all lower-case
_PREPROC = [_STRICT, _WARN, _NOT_STRICT, _KEYS_LOWER, _KEYS_UPPER, _ONE_INDEXED,
            _ZERO_INDEXED, _AUTO_INDEX]

# Units: Not case-sensitive but must be lower case here:
_UNITS = 'units'
_KNOWN_UNITS = ['ms', 'sec', 'utime', # time: milliseconds, seconds, unix-time (sec)
               'cm',  # distance: centimeters
               'deg', # degrees (eg, visual angle)
               'hz',  # Hertz
               'pix', # pixels (e.g., image or screen dimensions)
               'norm', # norm units: -1 to +1 inclusive
               'rgb', 'dkl', 'lms', # color space
               'percent',  # 0 to 100 inclusive
               #'likert',  # Likert scale?
               'tf', 'yn', 'bool', # True-False, yes-no, boolean
               'hex', 'base64', # hexadecimal (base 16), base 64 (text encodings)
               #'utf8', # utf-8 (encoding)
               _UNITS
               ]

# Regular expressions:
_valid_var_re = re.compile(r"^[a-zA-Z_][\w]*$")  # a string is a legal variable name
_bad_key_re = re.compile(r"[^a-z0-9.+, _]", re.I)  # non-OBF character (for a key)
_good_key_re = re.compile(r"^[a-z_][a-z0-9.+,\s_]*:\s+", re.I) # the line contains a good key
_almost_good_key_re = re.compile(r"^[a-z_][a-z0-9.+,\s_]*:[^\s]+", re.I) # lacks space after colon
_two_dots_re = re.compile(r"\..*\.")  # two '.' anywhere
_special_key_re = re.compile(r"^=.+=$")  # string is '=' first and last, with something in between
#_quoted_int_re = re.compile(r"^_\d+_$")  # string consists of digit(s) between underscores

_label_dot_units_re = re.compile(r"^([a-zA-Z_][^.]*)\.(.+)$")

class OBF_Load(dict):
    """Class for parsing a file-like data source; OBF text -> internal data.
    
    Parses from a data source (opened file, StringIO):
    - self.data   <- data structure
    - self.source <- repr of data source
    - self.report <- conversion warning & error messages
    - self.time   <- code timing profile
    - self.prepro <- preprocessing that was applied
    - self.yaml   <- yaml parser details
    
    Notes:
    - quote characters seem to mess with YAML parsing
      to use '123' (string) as a key for a dict instead of as an integer, use _123_ -> ['123'] 
      but then can't use _123_; maybe needs a preprocessing directive?
    
    Still needs:
    - better bad-key detection: get errors, but can be cryptic
      _0_: 2  ->  '0' = 2?
      single digit key ==  wonky TypeError in ignoreKeys
      
    - quoted int not working for OBF keys (only secondary keys)
    - more checking (only one =Session=, etc)
    - standardize .report[] messages --> warn, quiet, strict
    - provide usage examples
    - provide tests
    
    Eventually add ways to create OBF documents:
    - routines for creating different sections (i.e., conversion to OBF)
    
    Someday think about:
    - YAML does not require --- and ...; maybe good to check if they are in source
      good to require them be written by any function that emits OBF
    """
    def __init__(self, source, custom_actions={}, save_timing=False):
        """
        """
        # initialize timing profile:
        self.time = []
        self.time.append(('start',time.time()))
        self.time.append(('obf-load_start',time.time()))
        
        dict.__init__(self) # at first a dict made sense, but things have evolved; unclear now
        self.source = str(source)  # save the name / repr of the source
        
        self.report = [] # container for warnings and other notes
        
        # save info about the underlying YAML parser used for this OBF parsing:
        self.yaml = {}
        self.yaml['__name__'] = yaml.__name__
        self.yaml['__version__'] = yaml.__version__
        try:
            self.yaml['__with_libyaml__'] = yaml.__with_libyaml__
        except AttributeError:
            self.yaml['__with_libyaml__'] = '(not applicable)'
        
        # read only once from the source:
        raw_text = source.readlines()
        
        # here could search for --- <stuff> ..., and split into multiple sources
        #yaml_opener = [i for i, line in enumerate(raw_text) if line.startswith('---')]
        #yaml_closer = [i for i, line in enumerate(raw_text) if line.startswith('...')]
        # check for good openers & closers, non-overlapping
        
        # for multiple documents per file, refactor moving data{dict} to data[0]{dict}
        #self.data = []
        # loop:
        #     next_raw_text = chunk between first yaml_opener and first yaml_closer
        #     self.data.append() = ..
        
        # look before leaping:
        self.initial_checks(raw_text)
        self.data, self.prepro = self.preprocess(raw_text)
        
        # everything is 'key: value' pairs:
        self.parse_keys()
        
        # merge custom key:actions into default, then parse all values
        hot_keys = dict(_get_key_actions(), **custom_actions) 
        self.parse_values(hot_keys)
        
        # self.adjust_indices()  # ?? should ONE_INDEXED delete the actual [0] indices?
        
        # reporting and strictness level:
        self.report = list(set(self.report))  # remove redundant
        if _STRICT in self.prepro:
            pass # if 'ERROR' in any message, nullify self.data
        if _NOT_STRICT in self.prepro:
            pass # remove 'ERROR' and 'WARNING' message from self.report
        
        if not save_timing:
            del self.time
        else:
            #  format the timing tuples:
            self.time.append(('obf-load_end',time.time()))
            self.time[1:len(self.time)] = ["%7.3f = %s" %(self.time[i][1] - self.time[0][1],
                                                self.time[i][0]) for i in range(1,len(self.time))]
            self.time.pop(0) # remove the initial reference point time-zero
        
    def __str__(self):
        return '<data as OBF_Load()ed from '+self.source+'>'
    def __repr__(self):
        return str(self)
    
    def initial_checks(self, raw_text):
        '''Perform some basic validations.
        '''
        key_lines = [(i, line) for i, line in enumerate(raw_text) if not line.startswith(' ')]
        special_lines = [line for i, line in key_lines if line.startswith('=')]
        
        header = [line for line in special_lines if line.startswith(_HEADER)]
        if len(header) > 1:
            raise AttributeError, "OBF: ERROR: can only be one %s section" % _HEADER
        if len(header) == 0:
            raise AttributeError, "OBF: ERROR: needs a %s section" % _HEADER
        
        session = [line for line in special_lines if line.startswith(_SESSION)]
        # if...
        subject = [line for line in special_lines if line.startswith(_SUBJECT) or line.startswith(_PARTICIPANT)]
        # if...
        
        # avoid cryptic errors from YAML if colon-but-not-whitespace:
        colon_nonwhitespace = [i for i, line in key_lines if _almost_good_key_re.match(line)]
        for i in colon_nonwhitespace:
            key = raw_text[i][:raw_text[i].find(':')]
            self.report.append("OBF: WARNING: adding space after colon for key '%s'" % key)
            raw_text[i] = raw_text[i].replace(':', ': ')
        
    def preprocess(self, raw_text):
        '''text wrangling: find and apply preprocessing directives from =Header=
        '''
        # only need to work with lines having keys
        key_lines = [(i, line) for i, line in enumerate(raw_text) if _good_key_re.match(line)]
        
        # standardize / clean the text in keys:
        _clean_key_re = re.compile(r"^([a-z0-9_][a-z0-9.+, _]*[a-z0-9_])\s*:\s+", re.I)
        for i, line in key_lines:
            # skip one character keys:
            if line.replace(' ','').find(':') == 1:
                continue 
            match = _clean_key_re.match(line) # capture the key, no trailing white space
            clean_key = match.group(1).replace(',', '+')
            clean_key = re.sub(r"\s*\+\s*",'+', clean_key)
            # replace the orig key with a cleaned-up version of itself:
            raw_text[i] = re.sub(r".*:", clean_key+':', raw_text[i]) 
        
        # do a first yaml conversion to get preprocessing directives:
        text = '\n'.join(raw_text)
        self.time.append(('start yaml-load',time.time()))
        data0 = yaml.safe_load(text)
        self.time.append(('end yaml-load (with_libyaml = %s)' %
                            str(self.yaml['__with_libyaml__']), time.time()))
        
        prepro = []
        if 'preprocess' in data0[_HEADER].keys():
            prepro = data0[_HEADER]['preprocess']
            if prepro is None:
                prepro = []
            if type(prepro) == str:
                prepro = prepro.split(',')
            elif type(prepro) != list:
                self.report.append("OBF: 'preprocess: %s' not understood, so ignored" % str(prepro))
            prepro = map(lambda s: s.lower().strip().lstrip(), prepro)
            # check for unknown pre-proc
            if set(prepro).difference(_PREPROC):
                self.report.append("OBF: 'preprocess: %s' not understood, so ignored" %
                                   ', '.join(list(set(prepro).difference(_PREPROC))) )
            if _WARN in prepro:
                self.report.append("OBF: '%s' not implemented yet" % _WARN)
        
        # do pre-processing; yaml.load() again if things were auto_indexed:
        if len(prepro) > 0:
            obf_keys = set(data0.keys()).difference(set(_SPECIAL))
            key_lines = [(i, line) for i, line in enumerate(raw_text) if _good_key_re.match(line)]
            
            self.base_index = 1
            if _ZERO_INDEXED in prepro:
                self.base_index = 0
            if _AUTO_INDEX in prepro:
                # this does only the right-most loop; other loops are ambiguous
                for key in obf_keys:
                    matching_lines = [i for (i, line) in key_lines if line.find(key+':')==0]
                    if len(matching_lines) > 1:
                        # append increasing integers if more than one line
                        for k, linenum in enumerate(matching_lines):
                            raw_text[linenum] = raw_text[linenum].replace(key, key + '.' + str(k + self.base_index))
                # reload everything, now that lines have been disambiguated
                text = '\n'.join(raw_text)
                self.time.append(('start yaml-load #2',time.time()))
                data0 = yaml.safe_load(text)
                self.time.append(('end yaml-load #2',time.time()))
                obf_keys = set(data0.keys()).difference(set(_SPECIAL))
            if _KEYS_LOWER in prepro:
                for key in obf_keys:
                    if key != key.lower():
                        data0[key.lower()] = data0[key]
                        del data0[key]
            elif _KEYS_UPPER in prepro:
                for key in obf_keys:
                    if key != key.upper():
                        data0[key.upper()] = data0[key]
                        del data0[key]
        
        self.time.append(('end preprocess', time.time()))
        return data0, prepro
            
    def parse_keys(self):
        """
        inspect & process every key; expand valid keys as dimenions of self.data
        """
        # get all keys that are not special 
        nonspecial_keys = set(self.data.keys()).difference(set(_SPECIAL))
        
        # some keys might look special but are not, so treat as comments:
        ignore_keys = [k for k in nonspecial_keys if _special_key_re.match(k)]
        for key in ignore_keys:
            self.report.append("OBF: ignoring key '%s'" % key)
            del self.data[key]
        
        # all OBF keys, left justified in the file:
        obf_keys = set(self.data.keys()).difference(set(_SPECIAL))
        
        # filter regular keys:
        bad_keys = [k for k in obf_keys if _bad_key_re.search(k)]
        simple_keys = [k for k in obf_keys if _valid_var_re.match(k)]
        complex_keys = obf_keys.difference(set(simple_keys))
        
        # expand keys for nested loops (list or dict)
        for key in complex_keys:
            if key in bad_keys:
                self.report.append("OBF: ignoring key '%s'" % key)
                del self.data[k]
                continue
            name, index = key.split('.',1)
            if index.lower() == 'units':
                continue
            if index.lower() in _KNOWN_UNITS:
                if hasattr(self.data, name):
                    self.report.append("OBF: ERROR '%s' has units '%s', but key conflicts with existing key" % (key, index.lower()))
                else:
                    self.report.append("OBF: treating '%s' as %s with units %s" % (key, name, index.lower()))
                    self.data[name] = copy.deepcopy(self.data[key])
                    self.data[name+'.units'] = index
                    del self.data[key]
                continue
            #if _quoted_int_re.match(index):
            #    index = str(index.replace('_', ''))
            # parse each sub-item of the complex key: eg: name1.index1+name2.index2+...+nameN.indexN
            k2 = key # will nibble k2 down to nothing
            name_indices = [] # to contain (name, index) tuples
            while k2.find('+')>-1:
                left_end, k2 = k2.split('+',1) # nibble away
                if left_end.find('.') == -1:
                    raise AttributeError, "OBF: complex key '%s' is missing a '.'" % key
                if _two_dots_re.search(left_end):
                    raise AttributeError, "OBF: complex key '%s' has too many '.'" % key
                # build up list of parts, traverse it later
                name_indices.append(self._get_name_index(left_end, key))
            # do the last one:
            name_indices.append(self._get_name_index(k2, key))
            
            # "move" datum to its new place via copy, add, & delete orig:
            datum = copy.deepcopy(self.data[key])
            self._add_datum(name_indices, datum, key)
            del self.data[key]
        
        self.time.append(('end parse keys', time.time()))
        
    def _get_name_index(self, left_end, key):
        """returns a tuple (name, index), after checking that its reasonable
        
        used by parse_keys()
        """
        name, index = left_end.split('.')
        if re.match(r"^\d+$", index):
            # all numeric:
            index = int(index)
        elif re.match(r"^\d+[^\d]+", index):
            # not all numeric but starts with digit:
            raise AttributeError, "OBF: bad index '%s' in %s" %(index, key)
        else:
            index = str(index)
        return (name, index)
    
    def _add_datum(self, name_indices, datum, key):
        '''
        Given a single data point, add it to self.data. The interesting part is to
        grow / expand self.data to accomodate the structure implied by the given
        (name, index) pairs, which indicate nested lists, dicts, or a combination.
        
        The request is to place a single data point in a multi-dimensional 
        space. Some of the dimensions may not exist at all yet, so they have
        to be created. The dimensions can be ordered (lists) or unordered (dicts),
        or a mixture. There is no constraint on the number of such dimensions.
        
        More detail: given a list of (name, index) tuples, convert it into a data 
        structure within self.data, accepting an aribtrary number of reference
        tuples (= dimensions). at each step, the type (list or dict) is inferred
        from the type of its index.
        
        Strategy: traverse the existing data structure starting from a known-good
        root, self.data, at each point check for the next dimension, where (name,
        index) are always pairs):
            self.data[n][i]
            self.data[n][i] [n][i]
            self.data[n][i] [n][i] ... [n][i] = datum
        
        Implementation: goes list-by-list building up a string (s_data_build_string)
        to instantiate non-existing but required lists / dicts. after the dimensions 
        are known to exist or newly created via exec(), finally exec() the build-string,
        assigning datum to it. This places a single value in the data structure.
        
        Implied items are created and set to None, namely list elements that have
        a lower index value that the current item but have not yet been set explicitly.
        These will either get filled in later with a subsequent datum, or will
        just remain None, indicating a missing value.
        
        Maybe there's a simpler way to do it, possibly after all items have been 
        parsed (rather than item by item on the fly, as done here).
        
        Used only by parse_keys()
        '''
        
        s_data_build_string = 'self.data'
        while len(name_indices):
            # NAME is always a key for a dict; INDEX is either an int (if name 
            # refers to a list) or a str (if name refers to a dict)
            name, index = name_indices.pop(0) # list of tuples from _get_name_index()
            if index == 0 and self.base_index == 1:
                self.report.append("OBF: WARNING: '%s' requested, but index 0 received" % _ONE_INDEXED)
            s_data_build_string += '['+repr(name)+']'
            try:
                eval(s_data_build_string)
                is_existing = True
            except KeyError:
                is_existing = False
            except TypeError:
                raise TypeError, "OBF: ERROR: ambiguity in '%s': conflicting data-types, key '%s'" % (self.source, key)
            
            if is_existing:
                # make tmp a reference to the currently end-most list or dict:
                exec('tmp='+s_data_build_string)
                # being a reference, we can change tmp to change self.data[][]...[][]:
                if type(index) == int and type(tmp) == list:
                    # lengthen the list as needed:
                    while len(tmp) < index+1:
                        tmp.append(None)
                    if tmp[index] is None:
                        tmp[index] = {}
                elif type(index) == str and type(tmp) == dict:
                    # ensure that index is a key of name; init it if its a new key
                    if not index in tmp.keys():
                        tmp[index] = {}
                else: # mismatch, specifed in the data source
                    raise TypeError, "OBF: ERROR: ambiguity in '%s': conflicting data-types, key" % self.file
                
            else: # need a new list or dict
                if type(index) == int:
                    # new empty list, of minimum required length (index):
                    exec(s_data_build_string+'=[None for i in range('+str(index+1)+') ]')
                    exec(s_data_build_string+'['+repr(index)+']={}')
                else:
                    # new empty dict referenced by index as a key
                    exec(s_data_build_string+'={'+repr(index)+': {}}') 
            s_data_build_string += '['+repr(index)+']'
        exec(s_data_build_string+'='+repr(datum))
        
    def parse_values(self, hot_keys):
        """Inspect and process every value, descending recursively.
        
        The "hot_keys" do the work. They consist of key: function pairs, as defined
        by a merge of the defaults (from _get_key_actions) + custom hot_keys.
        """
        def walk_values(this_level):
            """
            1. trigger actions based on keys
            2. remove .units '.ms' from key and make an extra key 'var.units: ms'
            """
            if type(this_level) == list:
                for item in this_level: # or this_level[self.base-index:]?
                    if type(item) in [list, dict]:
                        walk_values(item)
                    
            elif type(this_level) == dict:        
                for key in this_level.keys():
                    status = None
                    for regex in hot_keys.keys():
                        # first match wins, not ordered
                        if regex == key: # then regex is just a normal string
                            status = hot_keys[regex](this_level, key, self)
                            break
                        elif regex[0] == '^' and regex[-1] == '$' and re.match(regex, key):
                            status = hot_keys[regex](this_level, key, self)
                            break
                    if status:
                        for k in status:
                            if k == 'new_key': key = status['new_key']
                            # if return-code: take-action[x]
                    if type(this_level[key]) in [list, dict]:
                        walk_values(this_level[key])
            else:
                assert False, "OBF: BUG in walk_values(): received a '%s'" % type(this_level)
        walk_values(self.data)
        self.time.append(('end parse values', time.time()))

class OBF_Dump(object):
    """Class for creating an OBF file-like data source; OBF text -> internal data.
    
    """
    def __init__(self):
        pass
    def dump(self):
        """ might want to use "default_flow_style=False"
        >>> print yaml.dump(yaml.load(document), default_flow_style=False)
        a: 1
        b:
          c: 3
          d: 4
        """
        pass
    def write(self):
        pass
    def fluch(self):
        pass
    def write_header(self):
        pass
    def write_session(self):
        pass
    def write_subject(self):
        pass
    
    
def _get_key_actions():
    """Returns a dict of default 'hot keys' = key + actions to be triggered.
    
    UNRESOLVED: being a dict is unordered, and it might be useful to know
    the order in which items are tried. On the other hand, it might actually be good to
    disallow order, so that matches can (must) have one and only one possible
    interpretation. 
    
    This allows for extensions in terms of custom (key: function) dict entries.
    The default keys are only semi-reserved, because they can be over-ridden by
    passing a different binding to custom_actions, when calling load(source, custom_actions={} )
    
    Keys can be given as a literal string to match, or as a regular expression.
    If a regex, it must including a leading ^ and ending $ to match the entire string;
    Keys that lack both a leading ^ and ending $ are simply compared using ==. 
    
    def some_action(this_dict, this_key, this_obj):
    - this action was triggered by 'this_key' of 'this_dict' 
    - typically do something with the value, this_dict[key], not the key
    - can also update this_dict or this_obj (eg, this_obj.report -> self.report)
    - return ('flag', a_value)
    """
    def convert_digits_as_str(this_dict, this_key, this_obj):
        # convert '_123_' to '123', to allow digits as a str in dict keys
        new_key = this_key.replace('_', '') # leave as str, only digits
        this_dict[new_key] = copy.deepcopy(this_dict[this_key])
        del this_dict[this_key]
        return {'new_key': new_key}
    def process_units(this_dict, this_key, this_obj):
        # interpret name.label as a name with units of label
        match = _label_dot_units_re.match(this_key) # captures
        if match:
            new_key = match.group(1)
            units = match.group(2)
            if units.lower() == _UNITS:
                return
            if units.lower() in _KNOWN_UNITS:
                units = units.lower()
            this_dict[new_key] = copy.deepcopy(this_dict[this_key])
            this_dict[new_key+'.units'] = units
            del this_dict[this_key]
            return {'new_key': new_key}
        else:
            this_obj.report.append("OBF: WARN: bad units for '%s." % this_key)
    def screen_random_seed(this_dict, this_key, this_obj):
        if this_dict[this_key] == 'None':
            this_obj.report.append("OBF: WARNING: ambiguous random_seed 'None'")
    def screen_mouse(this_dict, this_key, this_obj):
        mouse = this_dict[this_key]
        if type(mouse) == dict:
            if not 'x' in mouse and not 'y' in mouse:
                if 'pos' in mouse and type(mouse['pos'])==list and len(mouse['pos'])==2:
                    return
                else:
                    this_obj.report.append("OBF: ERROR: mouse lacks (x,y) or pos[]")
    key_action_dict = {
        # 'trigger': function_reference,
        'random_seed': screen_random_seed,
        'mouse': screen_mouse,
        r"^_\d+_$": convert_digits_as_str,
        r"^[a-zA-Z_].*\..+$": process_units
        #'key': screen_key
        }
    return key_action_dict

# Example of a custom key:action dict, here will nullify all default actions:
def clear_default_actions():
    """Returns a custom key:action dict with all default keys having action == pass.
    
    If this dict is used as
        OBF_Load(source, custom_actions=obfp.clear_default_actions())
    it overrides the default key:actions, so the defaults are effectively ignored. 
    One could get this dict, and then add to it, and so construct a completely 
    custom key: action dict, without any of the usual defaults.
    """
    def _do_nothing(this_dict, this_key, this_obj):
        pass
    key_action_dict = {}
    for key in _get_key_actions():
        key_action_dict[key] = _do_nothing
    return key_action_dict

def example1():
    return '''
=Header=:
    encoding: utf-8  # of this file
    default units: sec
    format: OBF v0.1    # merely informative
    
    preprocess:  one_indexed    # parser directives
    program: PsychoPy2  # program used to create the data file
    version: 1.64.00    # string
    
=Session=:
    experiment:
        name: my_script.py  # == the name of the script used to generate this data file
        authors:  # string or list of strings; empty (as it is here) will parse as 'None'
        sha1.hex: 044db3cbb2b27a09ce6bbb2a1d9988a5e4cc1571
            # sha1 (hex-encoded) digest of my_script.py
        script.base64:
            # a base64-encoded copy of my_script.py, stashed here in the data file
    session_start.utime: 1303844359.088219  # unix time = date + time
    date: 2011-04-26    # redundant but nice to have human-readable too
    time: 09:19.45.230
    computer: scan-mac03
    scanner:
        TR.sec: 2.000  # float
        scanner: MRRC timtrioa  # string
    random_seed: None

=Subject=:
    code: tr1234  # string; multiple subject codes are possible, [code1, code2]
    sex: male
    age: 23
    group: A
    consenter: XYZ # person administering informed consent
    tester: XYZ # person who administered the tasks, often same as consenter

welcome:
    stimulus: Welcome. In this study you will do some cool stuff and get paid.
    
consent:
    stimulus: Press 'y' to agree to participate.
    response:
        key: y
        
instructions:
    onset: 0.042
    duration: 6.221
    stimulus: The scanner will start in just a few seconds.

loop.1 + trial.1:
    onset: 12.321
    tag: press2
    stimulus: press 2
    response:
        key: 2
        correct: True
        RT: 0.654
    
loop.1 + ITI.1:
    onset: 13.321
    duration: 5.000
    
loop.1 + trial.2:
    onset: 18.321
    tag: press2
    stimulus: press 2
    response:
        key: 2
        correct: True
        RT: 0.654
    
loop.1 + ITI.2:
    onset: 23.321
    duration: 5.000
    
loop.2 + trial.0002:
    onset: 18.345
    tag: press2
    stimulus: press 2
    response:
        key: 3
        correct: False
        RT: 0.444
    
loop.2 + ITI.2:
    onset: 19.321
    duration: 3.000

loop.0: 1

debriefing:
    stimulus: How was that?
    response:
        # a list (-) of multi-line strings (|); indentation matters
        - | 
            it was kind of noisy in the scanner
            my back is a little sore
        - |
            it was cool to see
            my brain

# lists as data values:
multiple_mouse_clicks:
    onset: 122.43
    stimulus: click 5 times
    tag: multiple mouse
    mouse:
        click_on: release
        sample: clicks  # vs frames
        # 5 clicks => lists of length 5
        button: [left, left, middle, right, right]
        xx: [10, 20, 30, 40, 50]  
        y: [20, 30, 40, 50, 70]
        RT.ms: [543, 1033, 3449, 5467, 6587] # units can be applied to the list 
        wheel_rel: [0, 0, 0, 0, 0]
        
# Deeply nested loops & dicts are possible
# here is a single data point, value == 'vroom':
list_of_lists.0+b.0+c.0+d.0+e.0+f.0+g.0+h.0+i.0+j.0+k.0+l.0+m.0+n.0+o.0+p.0+q.0+r.0+s.0+t.0+u.0+v.0+w.0+x.0+y.0+z.0: vroom
# and again
dict_of_dicts.a+b.b+c.c+d.d+e.e+f.f+g.g+h.h+i.i+j.j+k.k+l.l+m.m+n.n+o.o+p.p+q.q+r.r+s.s+t.t+u.u+v.v+w.w+x.x+y.y+z.z: vroom

# more typical trial structure, several loops, multiple trials
trial.1 + text.red + color.blue:
    response: blue
    rt.ms: 765
trial.2 + text.red + color.blue:
    response: blue
    rt.ms: 765
# ...
#trial.999 + text.red + color.blue:
#    response: blue
#    rt.ms: 765

# note that items [0..998] will be set to None -- their presence is implied by trial.999

zz10.9:8 # illegal YAML syntax, but warn and correct (add a space) 
zz10.units: ms

zzz._1_:
    1111

=Footer=:
    exit_status: normal
    session_end.utime: 1303998240.246597
'''

def test_OBF_Load():
    """Run tests.
    """
    data = OBF_Load(StringIO.StringIO(example1()))
    
    # test for expected parsing:
    assert 'zz10' in data.data.keys()
    assert len(data.data['list_of_lists']) == 1
    
    # test for expected error messages:
    assert "OBF: WARNING: adding space after colon for key 'zz10.9:8'" in data.report
    
    print 'all tests pass'
    
if __name__ == '__main__':
    #data = OBF_Load(open('example.obf'), custom_actions=clear_default_actions())
    data = OBF_Load(StringIO.StringIO(example1()),save_timing=True)
    
    #print data.data['zzz'] # test _1_ -> '1'
    #print data.time
    
    for k in data.data:
        print k, data.data[k]
    print data.report
    #test_OBF_Load()
    
    