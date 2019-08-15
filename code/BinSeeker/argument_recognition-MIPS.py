#-*- coding: utf-8 -*-

from __future__ import division
from idaapi import *
from idc import *
from idautils import *
from collections import defaultdict 
from itertools import izip 
import sys,os
import globalVariable
import Queue
import chardet
import operator
import copy
import function
import convertToIR
import segment
import database
import libFuncs
import graph
import randomInput
import math
import example
#import decompiler
#import find_switch

f = 0
stackAddr = 0xaaaaab0L
argRegisters = ["eax","ecx","edx"]
stackIdentifier = ["[esp","[ebp"]
repAddr = []#单独存放rep指令的地址
functionSet = set()
functionEBPBased = {}
doubleOperandsInstrs = ["mov","lea","lds","les","movzx","movsx"]
allFuncInstancesPath = {}
currentArgList = {}
currentArgList_stack = []
pushAndCallList = set()
is64bit_binary = False
isVulnerabilityProgram = False
hasDecompiler = True
programName = ""
fileName = ""
notDefinedFunctions = []


class Process_with_Single_Function(object):
    def __init__(self, func_t):
        self._num = 0
        self._Blocks = set()
        self._Blocks_list = []
        self._func = func_t
        self._block_boundary = {}
        self._offspringSet = {}#the successors of a basic block
        self._offspring = {}
        self._mapping = {}#key is ths start address of a basic block, value is its id
        self._addr_func = func_t.startEA #first address of function
        self._name_func = str(GetFunctionName(func_t.startEA)) # GetFunctionName(startEA) returns the function name
        self._ids = []
        self._endblocks = []
        self.allPaths = []
        self._init_all_nodes()
        
    
    # initial block_boundary , get every node's range of address
    def _init_all_nodes(self):
        
        flowchart = FlowChart(self._func)
        self._num = flowchart.size
        for i in range(flowchart.size):
            basicblock = flowchart.__getitem__(i)
            self._Blocks.add(basicblock.startEA)
            self._block_boundary[basicblock.startEA] = basicblock.endEA
            self._ids.append(basicblock.id)
            self._mapping[basicblock.startEA]=basicblock.id
            suc = basicblock.succs()
            list = []
            for item in suc:
                list.append(item.startEA)
            if len(list)==0:
                self._endblocks.append(basicblock.startEA)
                #list.append(((basicblock.startEA),(item.startEA)))            
            self._offspringSet[basicblock.startEA] = list


class Switch(object): 
     """IDA Switch 
  
     Access IDA switch data with ease. 
  
     Usage: 
  
         >>> my_switch = Switch(switch_jump_address) 
         >>> for case, target in my_switch: 
         ...     print "{} -> 0x{:08X}".format(case, target) 
  
     """ 
     def __init__(self, ea): 
         """Initialize a switch parser. 
  
         Args: 
             ea: An address of a switch jump instruction. 
         """ 
         self._ea = ea 
  
         results = self._calc_cases() 
  
         self._map = self._build_map(results) 
  
         self._reverse_map = self._build_reverse(self._map) 
  
     def _build_reverse(self, switch_map): 
         reverse_map = defaultdict(list) 
         for case, target in switch_map.iteritems(): 
             reverse_map[target].append(case) 
         return reverse_map 
  
     def _calc_cases(self): 
         si = idaapi.get_switch_info_ex(self._ea) 
         results = idaapi.calc_switch_cases(self._ea, si) 
         if not results: 
             raise exceptions.SarkNotASwitch("Seems like 0x{:08X} is not a switch jump instruction.".format(self._ea)) 
  
         return results 
  
     def _build_map(self, results): 
         switch_map = {} 
         for cases, target in izip(results.cases, results.targets): 
             for case in cases: 
                 switch_map[case] = target 
  
         return switch_map 
  
     @property 
     def targets(self): 
         """Switch Targets""" 
         return self._map.values() 
  
     @property 
     def cases(self): 
         """Switch Cases""" 
         return self._map.keys() 
  
     @property 
     def pairs(self): 
         """(case, target) pairs""" 
         return self._map.iteritems() 
  
     def __iter__(self): 
         """Iterate switch cases.""" 
         return self._map.iterkeys() 
  
     def __getitem__(self, case): 
         """switch[case] -> target""" 
         return self._map[case] 
  
     def get_cases(self, target): 
         """switch.get_cases(target) -> [case]""" 
         if target in self.targets: 
             return self._reverse_map[target] 
  
         raise KeyError("Target 0x{:08X} does not exist.".format(target)) 
  
  
     def is_switch(ea): 
         try: 
             switch = Switch(ea) 
             return True 
         except exceptions.SarkNotASwitch: 
             return False 

def identify_switch(startAddr,endAddr):
    casesList = []
    targetsList = []
    head_ea_List = []
    jumps_List = []
    jumpsEnd_List = []
    jumptable=dict()
    for head_ea in Heads(startAddr,endAddr):
        if idc.isCode(idc.GetFlags(head_ea)):
            switch_info=idaapi.get_switch_info_ex(head_ea)
            if(switch_info and switch_info.jumps!=0):
                print "function addr and name",hex(head_ea),idc.GetFunctionName(head_ea)
                print "element base",switch_info.elbase
                print "start of switch idiom", switch_info.startea
                print "jump table address", switch_info.jumps
                print "element_num",switch_info.get_jtable_size()
                print "element_size",switch_info.get_jtable_element_size()
                my_switch=Switch(head_ea)
                #for case,target in my_switch:
                print ('%s,%s\n'%(my_switch.cases, my_switch.targets))
                casesList.append(my_switch.cases)
                targetsList.append(my_switch.targets)
                head_ea_List.append(head_ea)
                jumps_List.append(switch_info.jumps)
                jumpsEnd_List.append(switch_info.jumps + switch_info.get_jtable_size() * switch_info.get_jtable_element_size())
    return head_ea_List, jumps_List, jumpsEnd_List, casesList, targetsList

def getABinaryInstr(startea, itemsize):  #\x88 style
    out = []  
    strr = '0000000'  
    for i in range(startea, itemsize+startea):  
        strq = str(bin(GetOriginalByte(i)))[2:]  
        n = len(strq)  
        strq = strr[0:8 - n] + strq     
        temp = hex(int(strq,2))[1:]#x8 or x88 style
        if len(temp) == 2:
            temp = temp[0]+ '0' + temp[1]
        temp = "\\" + temp   
        out.append(temp)
    #print "out:",out
    
    return  ("".join(out))

#get the whole instruction of ea location
def get_instruction(ea):
    '''
    newlist = []
    newlist.append(ua_mnem(ea))
    i = 0
    op = GetOpnd(ea,i)
    while not op == '':
        print (self.get_reference(ea,i))
        newlist.append(op)
        i+=1
        op = GetOpnd(ea,i)
    '''
    return idc.GetDisasm(ea)

def getRepBinaryInstrInOneAddr(addr,size):
    result = getABinaryInstr(addr,size)
    return "'" + result + "'"

def getAllBinaryInstrInOneNode(func_t,startEA,endEA):
    #print "=======getAllBinaryInstrInOneNode",startEA,"========="
    it_code = func_item_iterator_t(func_t,startEA)
    ea = it_code.current()
    binaryInstrs = []
    while (ea<endEA):
        #print get_instruction(ea)# assemble style
        instr = getABinaryInstr(ea, ItemSize(ea))# binary style
        #print instr
        binaryInstrs.append(instr)
        #see if arrive end of the blocks
        if(not it_code.next_code()):
            break
        ea = it_code.current()
    result = "'"
    for a in binaryInstrs:
        result = result + a 
    result = result + "'"
    print "getAllBinaryInOneNode:",result
    return result

def getAllAsmInstrInOneNode(func_t,startEA,endEA):
    #print "=======getAllAsmInstrInOneNode",startEA,"========="
    instr_list = []
    it_code = func_item_iterator_t(func_t, startEA)
    ea = it_code.current() 
    address = []
    while (ea < endEA):
        instr = get_instruction(ea)
        instr_list.append(instr)
        address.append(ea)
        if(not it_code.next_code()):
            break
        ea = it_code.current()
    #print "instr:"
    #print instr_list
    return instr_list,address

def getAllInstrAddrInOneFunction(func_t,startEA,endEA):
    #print "=======getAllAsmInstrInOneNode",startEA,"========="
    #instr_list = []
    it_code = func_item_iterator_t(func_t, startEA)
    ea = it_code.current() 
    address = []
    while (ea < endEA):
        #instr = get_instruction(ea)
        #instr_list.append(instr)
        address.append(ea)
        if(not it_code.next_code()):
            break
        ea = it_code.current()
    #print "instr:"
    #print instr_list
    return address

#return the dictionary
def getAllBlocksInFunction(func_t):
    #print "=======getAllBlocksInFunction:",GetFunctionName(func_t.startEA),"========="
    flowchart = FlowChart(func_t)
    allBlocks = {}     
    startAddr = func_t.startEA
    endAddr = func_t.endEA
    print "function start and end",hex(startAddr),hex(endAddr)
    for i in range(flowchart.size):
        basicBlock = flowchart.__getitem__(i)
        if basicBlock.startEA >= startAddr and basicBlock.startEA < endAddr:
            allBlocks[basicBlock.startEA]=basicBlock 
    #print "allBlocks"
    #for item in allBlocks.keys():
        #print item,hex(allBlocks[item].startEA),hex(allBlocks[item].endEA)
    return allBlocks#Objects

def getNewCFGIncludeCall(cfg, allBlocks, func_t):
    print "cfg",cfg
    global repAddr
    repAddr = []
    startEnd = {}#record the start and end of a basic block
    #print "allBlocks",allBlocks
    for address in allBlocks.keys():
        print "block address: ",hex(address)
        blockStart = address
        blockEnd = allBlocks[address].endEA
        addrs = getAllInstrAddrInOneFunction(func_t,blockStart,blockEnd)
        print "addrs",addrs
        count = 0
        start = blockStart
        startEnd[start]=blockEnd
        numCount = 0
        #for addr in addrs:
        while count < len(addrs):
            numCount = numCount + 1
            print "count: ",count
            print "numCount: ",numCount
            if get_instruction(addrs[count]).find("__libc_start_main") > 0:#找到了启动函数,记录下来并删除
                notDefinedFunctions.append(func_t.startEA)                
            if numCount == 99 or GetMnem(addrs[count])=="jal" or GetMnem(addrs[count])=="movs" or GetMnem(addrs[count])=="scas" or GetMnem(addrs[count])=="stos" or GetMnem(addrs[count])=="rdrand" or GetMnem(addrs[count])=="cmps":#cmps指的是repe cmpsb
                if count < (len(addrs)-2):
                    print "start addrss: ",hex(start)
                    originalSuccessors = cfg[start]#得到IDA的CFG的后继节点列表
                    print "originalSuccessors: ", originalSuccessors
                    cfg[start]= addrs[count + 2]#得到一个新的基本块，mips平台的调用后面一定要接一个move $at,$at指令
                    print hex(start),"---> new successor: ",hex(addrs[count + 2])
                    startEnd[start]=addrs[count + 2]
                    print hex(start),"---> start end: ",hex(addrs[count + 2])
                    start = addrs[count + 2]#新的基本块开始位置
                    startEnd[start]=blockEnd#新的基本块技术位置        
                    print "a new start and end: ", hex(start),hex(blockEnd)           
                    tempList = []
                    print "new cfg start: ",hex(start)
                    for i in originalSuccessors:
                        tempList.append(i)
                        print "new cfg end: ",hex(i)
                    cfg[addrs[count + 2]] = tempList#将原始的CFG后继节点接在新的块之后
                if numCount == 99:#Pyvex最大一次性转换99条指令
                    numCount = 0
                count = count + 1 
                numCount = numCount + 1                   
            count = count + 1
        #处理包含rep的指令
        for addr in addrs:
            #print "GetMnem: ",GetMnem(addr),hex(addr)
            if GetMnem(addr)=="movs" or GetMnem(addr)=="scas" or GetMnem(addr)=="stos" or GetMnem(addr)=="rdrand" or GetMnem(addr)=="cmps":#rep获取出来竟然是movs,repn scas一起使用;stos表示的是rep stosd
                #print "shenmeyisia"
                repAddr.append(addr)
    '''
    print "---------newCFG-------------"
    print "cfg"
    for item in cfg.keys():
        print hex(item),cfg[item]
        print
    print "startEnd"
    for temp in startEnd.keys():
        print hex(temp),hex(startEnd[temp])
    print "---------newCFG-------------"
    '''
    return cfg,startEnd,repAddr
    
def getCFG_OF_Func(func_t):#get the Control Flow Graph of the function , return a list in the form of [(current_block_startaddr:next_block_startaddr), ......]
    # if a function has only one node , it's cfg may be empty
    #flowchart for a function
    #print "=======getCFG_OF_Func",GetFunctionName(func_t.startEA),"========="
    flowchart = FlowChart(func_t)
    dict = {}
    for i in range(flowchart.size):
        list = []
        basicBlock = flowchart.__getitem__(i)
        suc = basicBlock.succs()
        for item in suc:            
            list.append(item.startEA)
        dict[basicBlock.startEA] = list
        #print basicblock.id,hex(basicblock.startEA),hex(basicblock.endEA)    
    #print "dict",dict    
    return dict

def getAllPath(cfg):
    pass

def depth_first_search(cfg,root=None):
    order = []
    visited = {}
    def dfs(node):
        visited[node] = True
        order.append(node)
        for n in cfg[node]:
            if not n in visited:
                dfs(n)
    if root:
        dfs(root)
    for node in cfg.keys():
        if not node in visited:
            dfs(node)
    print order
    return order

def isContainDot(value):
    index = value.find(".")
    if index != -1:
        return True
    else: 
        return False

def containSemicolonAndComma(value):
    index = value.find('; "')
    if index != -1:
        return True
    return False

def isString(value):
    index = value.find("\"")
    index1 = value.find("'")
    if index != -1 or index1 != -1:
        return True
    else:
        return False

def getOffsetWithEBP(content,size):
    #[ebp + arg_0]
    if (content.find("[ebp")!=-1):
        if size > 400000000:
            return 0
        else:
            return size
    else:
        return 0

    #return content.

def isDecimal(ch):
    if (ch >= '0' and ch <= '9') or (ch >="A" and ch <="F"):
        return True
    else:
        return False

def secondOrThird(value1,value2):
    string1 = value1
    string2 = value2    
    ch1 = value1[-1]
    if ch1 == 'h':
        string1 = value1[:-1]
    ch2 = value2[-1]
    if ch2 == 'h':
        string2 = value2[:-1]
    flag1 = 1
    flag2 = 2
    if string1 == "":
        flag1 = 0
    if string2 == "":
        flag2 = 0
    for temp in list(string1):
        if not isDecimal(temp):
            flag1 = 0
            break
    for temp in list(string2):
        if not isDecimal(temp):
            flag2 = 0
            break
    if flag1 == 1 and flag2 == 2:
        return 3
    elif flag1 == 0 and flag2 == 2:
        return 2
    elif flag1==1 and flag2 == 0:
        return 1
    else:
        return 0
    
def computeValue(value1,value2,withh):
    valueDecimal = 0
    if withh == 1:                
        if value1.find("h")!=-1:
            value1 = value1[0:-1]
        valueDecimal = int(str(value1),16)   
    elif withh == 2:
        if value2.find("h")!=-1:
            value2 = value2[0:-1]
        valueDecimal = int(str(value2),16)   
    elif withh == 3:
        if value1.find("h")!=-1:
            value1 = value1[0:-1]
        valueDecimal = int(str(value1),16)   
        if value2.find("h")!=-1:
            value2 = value2[0:-1]
        valueDecimal = valueDecimal + int(str(value2),16)  
    return valueDecimal
    
def getOffsetWithoutEBP(content,size):
    #[esp+2Ch+s2]
    count = content.count("+")        
    if (content.find("[esp")!=-1):
        if count == 0:
            return 0
        if count == 1:
            return size
        elif count == 2:
            valueDecimal = 0
            index1 = content.find("+")
            index2 = content.find("+",index1 + 1)
            value1 = content[index1+1:index2]
            value2 = content[index2+1:-1]
            withh = secondOrThird(value1,value2)
            valueDecimal = computeValue(value1, value2, withh)
            #print "valueDecimal",valueDecimal
            difference = size - valueDecimal
            if difference > 0:
                return difference
            else:
                return 0 
        elif count == 3:
            valueDecimal = 0 
            value = "0"
            index1 = content.find("+")
            index2 = content.find("+",index1 + 1)
            index3 = content.find("+",index2 + 1)
            value1 = content[index1+1:index2]
            value2 = content[index2+1:index3]
            withh = secondOrThird(value1,value2)
            valueDecimal = computeValue(value1, value2, withh)
            #valueDecimal = int(str(value),16)   
            #print "valueDecimal",valueDecimal
            difference = size - valueDecimal
            if difference > 0:
                return difference
            else:
                return 0 
    else:
        return 0

def isSameRegister(content):
    index1 = content.find(',')
    register1 = content[3:index1].strip()
    register2 = content[index1+1:].strip()
    if register1 == register2:
        return True
    else:
        return False
def isRegisterReadLeft(content):
    index = content.find(',')
    content = content[3:index].strip()
    if content.find("[eax")!= -1 or content.find("[edx")!=-1 or content.find("[ecx")!=-1:
        return True
    else:
        return False  

def isRegisterRead(content):
    #mov     edi, [eax+170h]
    index = content.find(',')
    content = content[index+1:].strip()
    if content.find("[eax")!= -1 or content.find("[edx")!=-1 or content.find("[ecx")!=-1:
        return True
    else:
        return False    
def getRegister(content):
    index = content.find(',')
    content = content[index+1:].strip()#[eax+12h]or [eax]
    index2 = content.find('[')
    index1 = content.find('+')
    if index1 == -1:#不含+
        index3 = content.find('-')
        if index3 == -1:#是否含-
            content = content[index2+1:-1]
            return content
        else:
            content = content[index2+1:index3]
            return content
    else:
        content = content[index2+1:index1]
        return content
    
def getString1(disam):#dd offset aDefault      ; "default"字符串传间接跳转问题
    index1 = disam.find(";")
    if index1 != -1:
        disam = "" + disam[index1 + 3: -1]
    else:
        disam = " "
    return disam
    
def getRegisterLeft(content):
    index = content.find(',')
    content = content[3:index].strip()
    index2 = content.find('[')
    index1 = content.find('+')
    if index1 == -1:#不含+
        index3 = content.find('-')
        if index3 == -1:#是否含-
            content = content[index2+1:-1]
            return content
        else:
            content = content[index2+1:index3]
            return content
    else:
        content = content[index2+1:index1]
        return content    
    
def isLibFunc_EAX_return(name):
    if name in libFuncs.linux_lib or name in libFuncs.char_return_type or name in libFuncs.char_pointer_return_type or name in libFuncs.int_return_type or name in libFuncs.int_unsigned_return_type or name in libFuncs.long_return_type or name in libFuncs.file_pointer_return_type:
        return True
    else:
        return False
    
def getNewArgsRegister(register):#将al等换成eax
    eaxRegister = ['eax','ax','ah','al']
    edxRegister = ['edx','dx','dh','dl']
    ecxRegister = ['ecx','cx','ch','cl']
    if register in eaxRegister:
        return "eax"
    elif register in edxRegister:
        return "edx"
    elif register in ecxRegister:
        return "ecx"
    else:
        return register
    
def getNewArgsRegisterList(tempList):
    for i in range(len(tempList)):
        tempList[i] = getNewArgsRegister(tempList[i])
    return tempList
    
def identifyArgs_AllPath(func_t):
    pass
    
def modifyStackTop(stack_vars, stackBelow):
    for item in stack_vars:
        item["offset"] = item["offset"] - stackBelow 

def get_function_stack_offset(start):
    try:
        stackBelow = 0
        flag = True#一旦遇到arg_0将flag改成False
        print "get_function_stack_offset"
        #获取函数内的所有栈偏移
        # find the stack frame
        stack = GetFrame(start)
        #print "stack:"
        #print stack
        stack_size = GetStrucSize(stack)
        print "stack_size:",stack_size
        # figure out all of the variable names
        # base is either ' s' ... saved register or ' r' ... return address
        base = GetMemberOffset(stack, ' s')
        print "base:",base
        if base == -1:
            base = GetMemberOffset(stack, ' r')
            print "base == -1"#代表没有被保存的寄存器
        if base == -1:
            # no ' s' no ' r' assume zero
            base = 0
            print "base == 0"#代表没有返回地址
        stack_vars = []
    
        for memberoffset in xrange(stack_size):
            print "memberoffset:",memberoffset
            previous = stack_vars[-1] if len(stack_vars) else None
            print "previous:",previous
            var_name = GetMemberName(stack, memberoffset)
            print "var_name:",var_name
            if not var_name or (previous and var_name == previous.get("name")):
                # skip that entry, already processed
                print "skip"
                continue
            if var_name == "var_4" and flag:
                stackBelow = GetMemberOffset(stack, var_name) + 4#实际上是局部变量和参数的分界线
                modifyStackTop(stack_vars,stackBelow)
                flag = False
            offset = GetMemberOffset(stack, var_name) - base - stackBelow#mips
            print "offset:",offset
            size = GetMemberSize(stack, memberoffset)
            if previous:
                diff = offset - previous['offset']
                previous['diff_size'] = diff
            stack_vars.append({'name': var_name,
                               'offset': offset,
                               'offset_text': '[bp%Xh]' % offset if offset < 0 else '[bp+%Xh]' % offset,
                               'size': size,
                               'diff_size': size})
        #print "stack_size:"
        #print stack_size
        print "stack_vars:"
        print stack_vars
        return stack_size, stack_vars
    except BaseException,e:
        print "失败识别栈参数：",GetFunctionName(start)
        return 0,[]

def identifyStackArgsForMIPS32(func_t):
    stack_size, stack_vars = get_function_stack_offset(func_t.startEA)
    stackArgs = set()
    for item in stack_vars:
        if item["offset"] >= 16:
             stackArgs.add(item["offset"])
    return stackArgs

def isContainRegisterArgs(instruction):
    registerArgs = ['$a0','$a1','$a2','$a3']
    if '$a0' in instruction or '$a1' in instruction or '$a2' in instruction or '$a3' in instruction:
        return True
    else:
        return False

def whichRegisterArg(operand):
    if '$a0' in operand:
        return '$a0'
    elif '$a1' in operand:
        return '$a1'
    elif '$a2' in operand:
        return '$a2'
    elif '$a3' in operand:
        return '$a3'

def identifyRegisterArgs(func_t):
    #print "---------args:",hex(func_t.startEA)
    name = str(GetFunctionName(func_t.startEA))
    global functionSet
    global pushAndCallList
    functionSet.add(name)
    if function.identifiedVisited_stack[name] == False:
        stackArgs = set()
        registerArgs = set()
        modifiedReg = set()
        instrAddrs = getAllInstrAddrInOneFunction(func_t,func_t.startEA,func_t.endEA)
        print "函数内所有指令："
        for addr in instrAddrs:
            print hex(addr),get_instruction(addr)
        for addr in instrAddrs:
            print hex(addr),get_instruction(addr)
            for i in range(3):
                type = GetOpType(addr,i)
                print type
                if type == 4:
                    valueAddr = GetOperandValue(addr,i)
                    print "valueAddr:",valueAddr
                if type == 2:#Memory Reference                       
                    valueAddr = GetOperandValue(addr,i) 
                    #print "disasm",idc.GetDisasm(valueAddr)
                    disam = idc.GetDisasm(valueAddr)
                    size = ItemSize(valueAddr)
                    value = 0
                    print "disam:",disam
                    print "size:",size
                    if size == 8:
                        value = GetDouble(valueAddr)
                        #print "original GetDouble",value
                        if math.isnan(value):
                            value = 0
                        #print "GetDouble",value
                    if size ==4:
                        if (valueAddr < segment.rodataSegment[1]) and (valueAddr >= segment.rodataSegment[0]):
                            infer = isContainDot(disam)
                            if infer == True and '.word' not in disam:
                                value = round(GetFloat(valueAddr),6)                       
                                #print "GetFloat",value
                            else:
                                value = int(Dword(valueAddr))
                                #print "GetInt",value
                        elif (valueAddr < segment.dataSegment[1]) and (valueAddr >= segment.dataSegment[0]):
                            infer = isContainDot(disam)
                            if infer == True and '.word' not in disam:
                                value = round(GetFloat(valueAddr),6)                       
                                #print "GetFloat",value
                            else:
                                value = int(Dword(valueAddr))
                                #print "GetInt",value    
                    print "valueAddr in type == 2",valueAddr                        
                    segment.constUsage[valueAddr] = value
                elif type ==5: #offset e.g.,-0x18, 字符串变量
                    instructions = get_instruction(addr)   
                    valueAddr = GetOperandValue(addr,i)   
                    disam = idc.GetDisasm(valueAddr)
                    print "valueAddr",valueAddr,"disam ", disam
                    if isString(disam):#isString(instructions)原先还有一个or条件          
                        isContainSC = containSemicolonAndComma(disam)
                        #print "isContainSC",isContainSC
                        if isContainSC:
                            value = getString1(disam)
                        else:                  
                            value = GetString(valueAddr)
                        #print "value",value
                        if value is None:
                            #print "enter value is None"
                            value = getString1(disam)
                        #print "source string",value
                        #print "encoding before",chardet.detect(value)
                        if value is None:
                            value = " "
                        if (valueAddr < segment.rodataSegment[1]) and (valueAddr >= segment.rodataSegment[0]):
                            value = changeEncoding(value)
                        elif (valueAddr < segment.dataSegment[1]) and (valueAddr >= segment.dataSegment[0]):
                            value = changeEncoding(value)
                        #print "value",value
                        print "valueAddr in type == 5 if ",valueAddr   
                        segment.constUsage[valueAddr] = value
                        #print "StringType",GetStringType(valueAddr)
                        #print "encoding after", chardet.detect(value)
                        #print "source string", GetString(valueAddr)
                        #print "encoding after string",value
                    else:
                        disam = idc.GetDisasm(valueAddr)
                        value = 0
                        size = ItemSize(valueAddr)
                        if size == 8:
                            value = GetDouble(valueAddr)
                            
                            #print "GetDouble",value
                        if size ==4:
                            if (valueAddr < segment.rodataSegment[1]) and (valueAddr >= segment.rodataSegment[0]):
                                infer = isContainDot(disam)
                                if infer == True and '.word' not in disam:
                                    value = round(GetFloat(valueAddr),6)                       
                                    #print "GetFloat",value
                                else:
                                    value = int(Dword(valueAddr))
                                    #print "GetInt",value
                                print "valueAddr in type == 5 else 1",valueAddr   
                                segment.constUsage[valueAddr] = value
                            elif (valueAddr < segment.dataSegment[1]) and (valueAddr >= segment.dataSegment[0]):
                                infer = isContainDot(disam)
                                if infer == True and '.word' not in disam:
                                    value = round(GetFloat(valueAddr),6)                       
                                    #print "GetFloat",value
                                else:
                                    value = int(Dword(valueAddr))
                                    #print "GetInt",value         
                                print "valueAddr in type == 5 else 2",valueAddr         
                                segment.constUsage[valueAddr] = value
            if isContainRegisterArgs(get_instruction(addr)):
                print "    contain"
                type1 = GetOpType(addr,0)
                type2 = GetOpType(addr,1)
                print "type1: ",type1,"type2: ",type2
                opcode = GetMnem(addr)
                if opcode in ['sw', 'sdl', 'sdr', 'swl','swr','sb','sd','sh','usd','usw','ush','sdxcl','swxcl']:#内存写指令
                    for i in range(2):
                        type = GetOpType(addr,i)
                        if i == 0 and type1 == 1:#type1 为1表示的是寄存器
                            register = GetOpnd(addr,i)
                            if isContainRegisterArgs(str(register)):#判断是否是参数寄存器
                                if register not in modifiedReg:
                                    if register == "$a3":
                                        return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                                    else:    
                                        registerArgs.add(register)
                        elif i == 0 and type1 != 1:
                            print "sw中的特殊情况"
                        elif i == 1 and isContainRegisterArgs(GetOpnd(addr,1)):#看第二个操作数是否含有对参数寄存器的读
                            register = whichRegisterArg(GetOpnd(addr,1))
                            if register not in modifiedReg:
                                if register == "$a3":
                                    return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                                else:    
                                    registerArgs.add(register)
                elif opcode in ['move','mfc0','mfc1','mtc0','mtc1','dmfc0','dmtc0','ldc1','lb','lbu','ld','ldl','ldr','lwl','lwr','lh','lhu','lw','lwu','uld','ulh','ulhu','ulw','ldxcl','lwxcl']:
                    for i in range(2):
                        type = GetOpType(addr,i)
                        if i == 0 and type1 == 1:#第一个参数是被写的位置
                            register = GetOpnd(addr,i)
                            if isContainRegisterArgs(str(register)):#判断是否是参数寄存器
                                modifiedReg.add(register)#这个寄存器被修改了
                        elif i == 0 and type1 != 1: #不是寄存器操作数
                            print "lw中的特殊情况"
                        elif i == 1 and isContainRegisterArgs(GetOpnd(addr,1)):#第二个参数是否有寄存器的读
                            register = whichRegisterArg(GetOpnd(addr,1))
                            if register not in modifiedReg:
                                if register == "$a3":
                                    return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                                else:    
                                    registerArgs.add(register)
                elif opcode in ['addu','addiu','daddu','daddiu','dsub','sub','dsubu','subu','and','andi','or','ori','xor','xori','nor','drol','dror','rol','ror','dsll','dsll32','dsllv','dsra','dsra32','dsrav','dsrl','dsrl32','dsrlv','sll','sllv','sra','srav','srl','srlv']:
                    type3 = GetOpType(addr,2)
                    if type3 != 0:#说明有三个操作数
                        for i in range(3):
                            type = GetOpType(addr,i)
                            operand = GetOpnd(addr,i)
                            if i == 0 and type == 1:
                                register = GetOpnd(addr,i)
                                if isContainRegisterArgs(str(register)):#判断是否是参数寄存器
                                    modifiedReg.add(register)#这个寄存器被修改了
                            elif (i == 1 or i == 2) and isContainRegisterArgs(operand):
                                register = whichRegisterArg(operand)
                                if register not in modifiedReg:
                                    if register == "$a3":
                                        return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                                    else:    
                                        registerArgs.add(register)
                    else:#说明有两个操作数
                        for i in range(2):
                            type = GetOpType(addr,i)
                            if i == 0 and type1 == 1:
                                register = GetOpnd(addr,i)
                                if isContainRegisterArgs(str(register)):
                                    if register not in modifiedReg:
                                        registerArgs.add(register)#先加进去，然后在添加到被修改的寄存器参数中
                                        modifiedReg.add("$a3")
                                        if register == "$a3":
                                            return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                            elif i == 0 and type1 != 1:
                                print "二元操作中的其他情况1"
                            elif i == 1 and type2 == 1:
                                register = GetOpnd(addr,i)
                                if isContainRegisterArgs(str(register)):
                                    if register not in modifiedReg:
                                        registerArgs.add(register)
                                        if register == "$a3":
                                            return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                            elif i == 1 and type2 == 5:#第二个操作数是立即数
                                pass
                            elif i == 1 and type2 != 1:
                                print "二元操作中的其他情况2"
                elif opcode in ['abs','dabs','dneg','neg','dnegu','negu']:#一元运算指令
                    print "opcode:",opcode
                elif opcode in ['b','bal','beq','beq1','beqz','beqz1','bge','bge1','bgeu','bgeu1','bgez','bgez1','bgt','bgt1','bgtu','bgtu1','bgtz','bgtz1','ble','ble1','bleu','bleu1','blez','blez1','blt','blt1','bltu','bltu1','bltz','bltz1','bne','bnel','bnez','bnezl']:
                    for i in range(2):
                        operand = GetOpnd(addr,i)
                        if isContainRegisterArgs(operand):
                            register = whichRegisterArg(operand)
                            if register not in modifiedReg:
                                registerArgs.add(register)
                                if register == '$a3':
                                    return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                elif opcode in ['movf','movt','movn','movz']:
                    print "特殊的move指令，",opcode
                elif opcode in ['dla','la','dli','li','lui']:
                    for i in range(2):
                        type = GetOpType(addr,i)
                        if i == 0 and type1 == 1:#第一个参数是被写的位置
                            register = GetOpnd(addr,i)
                            if isContainRegisterArgs(str(register)):#判断是否是参数寄存器
                                modifiedReg.add(register)#这个寄存器被修改了
                        elif i == 0 and type1 != 1: #不是寄存器操作数
                            print "li中的特殊情况"
                        elif i == 1 and isContainRegisterArgs(GetOpnd(addr,1)):#第二个参数是否有寄存器的读
                            register = whichRegisterArg(GetOpnd(addr,1))
                            if register not in modifiedReg:
                                if register == "$a3":
                                    return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                                else:    
                                    registerArgs.add(register)
                elif opcode in ['ddiv','ddivu','div','divu','divo','divou','dmul','mul','mulo','mulou','dmulo','dumlou','dmult','dmultu','mult','multu','drem','dremu','rem','remu','mfhi','mflo','mthi','mtlo']:
                    for i in range(2):
                        operand = GetOpnd(addr,i)
                        if isContainRegisterArgs(operand):
                            register = whichRegisterArg(operand)
                            if register not in modifiedReg:
                                if register == "$a3":
                                    return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                                else:    
                                    registerArgs.add(register)
                elif opcode in ['mfhi','mflo']:#从hi，lo寄存器中读值值到寄存器中
                    for i in range(2):
                        if i == 0 and type1 == 1:
                            register = GetOpnd(addr,i)
                            if isContainRegisterArgs(str(register)):#判断是否是参数寄存器
                                modifiedReg.add(register)#这个寄存器被修改了
                        elif i == 0 and type1 != 1:
                            print "mfhi中的异常情况"
                elif opcode in ['slt','sltu','slti','sltiu']:#slt $1,$2,$3, if $2<$3 $1=1 else $1 = 0
                    for i in range(3):
                        type = GetOpType(addr,i)
                        operand = GetOpnd(addr,i)
                        if i == 0 and type == 1:
                            register = GetOpnd(addr,i)
                            if isContainRegisterArgs(str(register)):#判断是否是参数寄存器
                                modifiedReg.add(register)#这个寄存器被修改了
                        elif (i == 1 or i == 2) and isContainRegisterArgs(operand):
                            register = whichRegisterArg(operand)
                            if register not in modifiedReg:
                                if register == "$a3":
                                    return set(),set(['$a0','$a1','$a2','$a3']),modifiedReg
                                else:    
                                    registerArgs.add(register)
                elif opcode in ['jal','jalr']:#函数调用
                    pushAndCallList.add(addr)
                    functionName = GetOpnd(addr,0)
                    print "call function:",functionName
                    if function.functionMap.has_key(functionName):
                        if functionName not in functionSet:#遍历时未遇到该函数
                            calleeStackArgs,calleeRegisterArgs,calleeModifiedReg = identifyRegisterArgs(function.functionMap[functionName])
                            tempRegisterArgs = calleeRegisterArgs - modifiedReg
                            registerArgs = registerArgs | tempRegisterArgs
                            modifiedReg = modifiedReg | calleeModifiedReg
                            if functionName in functionSet:
                                functionSet.remove(functionName)            
                        else:#之前出现过，现在又再次出现的函数
                            if function.identifiedVisited_stack[functionName]:#已经有结果了
                                argsList1 = function.args_stack[functionName]
                                calleeStackArgs = set(argsList1[0])
                                calleeRegisterArgs = set(argsList1[1])
                                calleeModifiedReg = set(argsList1[2])
                                #print "旧的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                                #print "被调的参数集合，被调的栈参数，被调的寄存器参数，被调的修改参数", calleeStackArgs, calleeRegisterArgs,calleeModifiedReg
                                #modifiedReg = modifiedReg | calleeModifiedReg
                                tempRegisterArgs = calleeRegisterArgs - modifiedReg
                                registerArgs = registerArgs | tempRegisterArgs
                                modifiedReg = modifiedReg | calleeModifiedReg
                                #print "新的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                            else:
                                pass
                else:
                    print "其他指令：",opcode
        function.identifiedVisited_stack[name]=True                                
        argsList = []
        argsList.append(list(stackArgs))
        argsList.append(list(registerArgs))
        argsList.append(list(modifiedReg))
        function.args_stack[name] = argsList
    else:
        argsList = function.args_stack[name]
        stackArgs = set(argsList[0])
        registerArgs = set(argsList[1])
        modifiedReg = set(argsList[2])
    return stackArgs,registerArgs,modifiedReg#实际上stackArgs没有用上，已经用其他方法实现了  

def identifyArgs(func_t):
    #不再使用，因为这种方法是找函数的所有路径，然后遍历每个路径，其实是很慢的（路径基数太大了），所以摒弃掉
    print "---------args:",hex(func_t.startEA)
    name = str(GetFunctionName(func_t.startEA))
    global functionSet
    functionSet.add(name)
    global allFuncInstancesPath

    if function.identifiedVisited[name] == False:
        print "visited: false"
        #print "stacksize ", GetFrameSize(func_t.startEA)
        stackArgs_all = set()
        registerArgs_all = set()
        modifiedReg_all = set()
        for path in allFuncInstancesPath[func_t.startEA].allPaths:  
            stackArgs = set()
            registerArgs = set()
            modifiedReg = set()#depth_first_search(cfg, startAddr)
            #for addr in path:
            length = 0
            while length < len(path):
                addr = path[length]  
                print hex(addr),get_instruction(addr)
                type1 = GetOpType(addr,0)
                type2 = GetOpType(addr,1)
                for i in range(2):
                    type = GetOpType(addr,i)
                    print "i",i
                    print "type",type
                    if type == 4:#base + index + displacement. e.g. [esp+arg_0]
                        print "offset",GetOperandValue(addr,i)
                        result = 0
                        if functionEBPBased[name]:#ebp based
                            result = getOffsetWithEBP(GetOpnd(addr,i), GetOperandValue(addr,i))
                        else:
                            result = getOffsetWithoutEBP(GetOpnd(addr,i), GetOperandValue(addr,i))
                        if result > 0:
                            stackArgs.add(result)
                        #判断是否能为寄存器读
                        if i == 1 and isRegisterRead(get_instruction(addr)):
                            register = getRegister(get_instruction(addr))
                            register = getNewArgsRegister(register)
                            if register not in modifiedReg:
                                registerArgs.add(register)
                                print "加入寄存器参数集合", register
                        '''
                        if (GetOpnd(addr,i).find("[ebp")!=-1 or GetOpnd(addr,i).find("[esp")!=-1)and GetOpnd(addr,i).find("arg_")!=-1:
                            #offset = getOffset(GetOpnd(addr,i),GetOperandValue(addr,i))
                            #stackArgs.add(offset)
                            stackArgs.add(GetOperandValue(addr,i))
                            print "加入栈参数集合",GetOperandValue(addr,i)
                            #print "operandValue:",GetOperandValue(addr,i)
                        '''
                    elif type == 3:# register indirect, base + index . e.g. dword ptr[esp],byte ptr [eax]
                        #print "operandValue:",hex(GetOperandValue(addr,i))
                        #print "opnd:",GetOpnd(addr,i)
                        instr = GetMnem(addr)
                        if i == 1 and isRegisterRead(get_instruction(addr)):
                            register = getRegister(get_instruction(addr))
                            register = getNewArgsRegister(register)
                            if register not in modifiedReg:
                                registerArgs.add(register)
                                print "加入寄存器参数集合", register
                        if instr == "cmp":
                            if i == 0 and isRegisterReadLeft(get_instruction(addr)):
                                register = getRegisterLeft(get_instruction(addr))
                                register = getNewArgsRegister(register)
                                if register not in modifiedReg:
                                    registerArgs.add(register)
                                    print "加入寄存器参数集合", register
                    elif type == 1:
                        register = GetOpnd(addr,i)
                        register = getNewArgsRegister(register)
                        instr = GetMnem(addr)
                        print "instr ",instr
                        if register in argRegisters:
                            if type2 == 0:#说明没有第二个操作数
                                if instr != "push" and instr!= "pop":
                                    if register not in modifiedReg:
                                        registerArgs.add(register)
                                        print "加入寄存器参数集合", register
                                        
                                    #else:
                                        modifiedReg.add(register)
                                        print "加入被修改的寄存器参数集合", register
                                #if instr == "pop":
                                    #modifiedReg.add(register)
                                    #print "加入被修改的寄存器参数集合", register
                                #elif instr == "push":
                                    #if register not in modifiedReg:
                                        #registerArgs.add(register)
                                        #print "加入寄存器参数集合，由于push的存在", register
                                if instr == "pop":
                                    if register in modifiedReg:
                                        modifiedReg.remove(register)
                                        print "在被修改的寄存器集合中弹出",register
                                elif instr == "push":
                                    print "push不需要特殊处理"
                            elif type2 !=0:#两个操作数
                                if instr == "xor":
                                    if isSameRegister(get_instruction(addr)):
                                        modifiedReg.add(register)#因为 test 和  cmp 不改变寄存器的值
                                        print "加入被修改的寄存器参数集合,由于xor的存在", register
                                    else:
                                        if i == 1 and register not in modifiedReg:
                                            registerArgs.add(register)
                                            print "加入寄存器参数集合,由于xor", register
                                        elif i == 0:
                                            if register not in modifiedReg:
                                                registerArgs.add(register)
                                                print "加入寄存器参数集合,由于xor", register
                                                modifiedReg.add(register)
                                                print "加入被修改的寄存器参数集合,由于xor的存在", register
                                    
                                else:
                                    print "被修改的寄存器参数",modifiedReg
                                    print "register ",register
                                    if (register not in modifiedReg):#i=0或等于1时都会判断是否会加入到寄存器参数中,但是mov指令除外                                    
                                        if not (i==0 and (instr in doubleOperandsInstrs)):
                                            registerArgs.add(register)
                                            print "加入寄存器参数集合", register
                                    if i == 0:#只有第一个操作数才能被改动，所有i=1时的第二个操作数不用处理,但是交换指令要除外
                                        if instr != "cmp" and instr != "test":
                                            modifiedReg.add(register)#因为 test 和  cmp 不改变寄存器的值
                                            print "加入被修改的寄存器参数集合", register
                                    if i == 1 and instr == "xchg":
                                        modifiedReg.add(register)#因为 test 和  cmp 不改变寄存器的值
                                        print "加入被修改的寄存器参数集合,由于xchg的存在", register
                                '''
                                if i == 1 and type1 == 1 and type2 == 1 and instr == "xor":#清空寄存器的值为0
                                    if register in registerArgs:
                                        registerArgs.remove(register)
                                    modifiedReg.add(register)
                                ''' 
                            else:#没有操作数
                                continue
                        else:
                            continue 
                        '''
                        register = GetOpnd(addr,i)
                        if register in argRegisters:
                            if i == 1 and register not in modifiedReg:# the second operand value may be the argument
                                registerArgs.add(register)
                                print "加入寄存器参数集合", register
                            else:# the first operand value may be modified
                                modifiedReg.add(register)
                                print "加入被修改的寄存器参数集合", register
                        '''
                    elif type == 2:#Memory Reference                       
                        valueAddr = GetOperandValue(addr,i) 
                        print "disasm",idc.GetDisasm(valueAddr)
                        disam = idc.GetDisasm(valueAddr)
                        size = ItemSize(valueAddr)
                        value = 0
                        if size == 8:
                            value = GetDouble(valueAddr)
                            print "original GetDouble",value
                            if math.isnan(value):
                                value = 0
                            print "GetDouble",value
                        if size ==4:
                            if (valueAddr < segment.rodataSegment[1]) and (valueAddr >= segment.rodataSegment[0]):
                                infer = isContainDot(disam)
                                if infer == True:
                                    value = round(GetFloat(valueAddr),6)                       
                                    print "GetFloat",value
                                else:
                                    value = int(Dword(valueAddr))
                                    print "GetInt",value
                            elif (valueAddr < segment.dataSegment[1]) and (valueAddr >= segment.dataSegment[0]):
                                infer = isContainDot(disam)
                                if infer == True:
                                    value = round(GetFloat(valueAddr),6)                       
                                    print "GetFloat",value
                                else:
                                    value = int(Dword(valueAddr))
                                    print "GetInt",value                            
                        segment.constUsage[valueAddr] = value
                    elif type ==5: #offset
                        instructions = get_instruction(addr)   
                        valueAddr = GetOperandValue(addr,i)   
                        disam = idc.GetDisasm(valueAddr)
                        print "valueAddr",valueAddr,"disam ", disam
                        if isString(disam):#isString(instructions)原先还有一个or条件
                            isContainSC = containSemicolonAndComma(disam)
                            print "isContainSC",isContainSC
                            if isContainSC:
                                value = getString1(disam)
                            else:                                              
                                value = GetString(valueAddr)
                            print "value",value
                            if value is None:
                                print "enter value is None"
                                value = getString1(disam)
                            print "source string",value
                            print "encoding before",chardet.detect(value)
                            if value is None:
                                value = " "
                            if (valueAddr < segment.rodataSegment[1]) and (valueAddr >= segment.rodataSegment[0]):
                                value = changeEncoding(value)
                            elif (valueAddr < segment.dataSegment[1]) and (valueAddr >= segment.dataSegment[0]):
                                value = changeEncoding(value)
                            print "value",value
                            segment.constUsage[valueAddr] = value
                            #print "StringType",GetStringType(valueAddr)
                            print "encoding after", chardet.detect(value)
                            #print "source string", GetString(valueAddr)
                            print "encoding after string",value
                        else:
                            disam = idc.GetDisasm(valueAddr)
                            value = 0
                            size = ItemSize(valueAddr)
                            if size == 8:
                                value = GetDouble(valueAddr)
                                
                                print "GetDouble",value
                            if size ==4:
                                if (valueAddr < segment.rodataSegment[1]) and (valueAddr >= segment.rodataSegment[0]):
                                    infer = isContainDot(disam)
                                    if infer == True:
                                        value = round(GetFloat(valueAddr),6)                       
                                        print "GetFloat",value
                                    else:
                                        value = int(Dword(valueAddr))
                                        print "GetInt",value
                                    segment.constUsage[valueAddr] = value
                                elif (valueAddr < segment.dataSegment[1]) and (valueAddr >= segment.dataSegment[0]):
                                    infer = isContainDot(disam)
                                    if infer == True:
                                        value = round(GetFloat(valueAddr),6)                       
                                        print "GetFloat",value
                                    else:
                                        value = int(Dword(valueAddr))
                                        print "GetInt",value                
                                    segment.constUsage[valueAddr] = value
                    elif type ==11:
                        print GetOperandValue(addr,i)      
                    else:#2--memory reference 5--immediate value
                        pass#if the visit is a global variable, then we may need a special solution 
                    if type == 7 or type == 6:#call or jmp, include near or far address
                        #print "Mnem",GetMnem(addr)
                        if GetMnem(addr)=="call":
                            functionName = GetOpnd(addr,i)
                            print "functionName:",functionName
                            if function.functionMap.has_key(functionName):
                                print "function call",functionName
                                print "functionName:",functionSet
                                if functionName not in functionSet:
                                    print "旧的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                                    storeCurrentArgs(name,stackArgs,registerArgs,modifiedReg)
                                    calleeStackArgs, calleeRegisterArgs,calleeModifiedReg = identifyArgs(function.functionMap[functionName])
                                    print "旧的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                                    print "被调的参数集合，被调的栈参数，被调的寄存器参数，被调的修改参数", calleeStackArgs, calleeRegisterArgs,calleeModifiedReg
                                    #modifiedReg = modifiedReg | calleeModifiedReg
                                    tempRegisterArgs = calleeRegisterArgs - modifiedReg
                                    registerArgs = registerArgs | tempRegisterArgs
                                    modifiedReg = modifiedReg | calleeModifiedReg
                                    print "新的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                                    if functionName in functionSet:#计算完这个函数的参数了，需要退出
                                        functionSet.remove(functionName)
                                else:#之前出现过，现在又有可能再次出现的函数
                                    if function.identifiedVisited[functionName]:#已经有结果了
                                        argsList1 = function.args[functionName]
                                        calleeStackArgs = set(argsList1[0])
                                        calleeRegisterArgs = set(argsList1[1])
                                        calleeModifiedReg = set(argsList1[2])
                                        print "旧的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                                        print "被调的参数集合，被调的栈参数，被调的寄存器参数，被调的修改参数", calleeStackArgs, calleeRegisterArgs,calleeModifiedReg
                                        #modifiedReg = modifiedReg | calleeModifiedReg
                                        tempRegisterArgs = calleeRegisterArgs - modifiedReg
                                        registerArgs = registerArgs | tempRegisterArgs
                                        modifiedReg = modifiedReg | calleeModifiedReg
                                        print "新的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                                    else:#"之前出现过，但是还没有计算完参数,获取已知的参数"
                                        calleeRegisterArgs,calleeModifiedReg = getCurrentArgs(functionName)
                                        tempRegisterArgs = calleeRegisterArgs - modifiedReg
                                        registerArgs = registerArgs | tempRegisterArgs
                                        modifiedReg = modifiedReg | calleeModifiedReg
                                        print "之前出现过，但是还没有计算完参数"
                                        print "新的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                                    #print "旧的参数集合，寄存器参数，修改的寄存器",registerArgs,modifiedReg
                            elif isLibFunc_EAX_return(functionName[1:]):#库函数
                                print "库函数调用",functionName
                                print "加入寄存器参数集合 eax"
                                modifiedReg.add("eax")
                length = length + 1
            stackArgs_all = stackArgs_all | stackArgs
            registerArgs_all = registerArgs_all | registerArgs
            modifiedReg_all = modifiedReg_all | modifiedReg
        function.identifiedVisited[name] = True
        argsList_all = []
        argsList_all.append(list(stackArgs_all))
        argsList_all.append(list(registerArgs_all))
        argsList_all.append(list(modifiedReg_all))
        function.args[name] = argsList_all
    else:
        print "visited: true"
        argsList_all = function.args[name]
        stackArgs_all = set(argsList_all[0])
        registerArgs_all = set(argsList_all[1])
        modifiedReg_all = set(argsList_all[2])
    return stackArgs_all, registerArgs_all,modifiedReg_all       

def storeCurrentArgs(name,stackArgs,registerArgs,modifiedReg):
    global currentArgList
    registerList = []
    registerList.append(list(registerArgs))
    registerList.append(list(modifiedReg))
    currentArgList[name] = registerList
    
def getCurrentArgs(name):
    global currentArgList
    if name in currentArgList.keys():
        registerList = currentArgList[name]
        return set(registerList[0]),set(registerList[1])
    else:
        return set(),set()

def decompile_func(ea):
    f = get_func(ea)
    if f is None:
        print "error in get_func"
        return False
    try:
        cfunc = decompile(f);
    except BaseException,e:
        print "decompile failure"
        print str(e)
        return False
    else:
        if cfunc is None:
            print "error in decompile"
            # Failed to decompile
            return False
    
        lines = []
        sv = cfunc.get_pseudocode();
        for sline in sv:
            line = tag_remove(sline.line);
            lines.append(line)
        #return "\n".join(lines)
        return lines[0]       

def getRegisterParametersFromFunctionPseudocode(funcStartAddr):
    declarationLine = decompile_func(funcStartAddr)
    if declarationLine == False:
        print "Failure during decompiling"
        return []
    else:
        print "line:",declarationLine
        index1 = declarationLine.find('(')
        if index1 != -1 :
            declarationLine = declarationLine[index1 + 1:-1]
        #print declarationLine
        parametersString = declarationLine.split(',')
        #print parametersString
        registerParameterList = []
        for item in parametersString:
            index2 = item.find('<')
            if index2 != -1:
                registerParameterList.append(item[index2+1:-1])
        return registerParameterList

def getFunctionsArgs():
    return set(),set(),set()

def storeNewCfg(db,cfgInfo):
    documents = []
    print "newcfg",cfgInfo
    for item in cfgInfo.keys():
        document = {}
        document["startAddr"] = item
        if isinstance(cfgInfo[item],list):
            document["num"] = len(cfgInfo[item])
            document["successors"] = cfgInfo[item]
        else:
            document["num"] = 1
            tempList = []
            tempList.append(cfgInfo[item])
            document["successors"] = tempList
        documents.append(document)
    database.insertManyForCfg(db,documents)

def removeDollar(registers):
    newRegisters = set()
    for item in registers:
        newRegisters.add(item[1:])
    return newRegisters

def processFunction(func_t,db):
    #if func_t.startEA == 134521027:
    global functionSet,notDefinedFunctions
    functionSet.clear()
    print "-------------------",GetFunctionName(func_t.startEA),"-----------------------"
    startAddr = func_t.startEA
    frameSize = GetFrameSize(func_t.startEA)
    #print "startAddr:",startAddr
    #print "frameSize",GetFrameSize(func_t.startEA)
    allBlocks = getAllBlocksInFunction(func_t)#allBlocks is a dictionary
    print "allBlocks:"
    for item in allBlocks.keys():
        print item, hex(item)
    cfg = getCFG_OF_Func(func_t)
    newCfg,startEnd,reps = getNewCFGIncludeCall(cfg, allBlocks, func_t)
    print "startEnd",startEnd
    storeNewCfg(db,copy.deepcopy(newCfg))
    print "newCFG:",newCfg
    for item in newCfg.keys():
        print hex(item)
        if isinstance(newCfg[item],list):
            print "    ",
            for i in newCfg[item]:
                print hex(i),
            print
        else:
            print "    ",hex(newCfg[item])
    print "startEnd",startEnd  
    for item in startEnd.keys():
        print hex(item), hex(startEnd[item])  
    for item in startEnd.keys():
        #instrInBlock,instrAddress = getAllAsmInstrInOneNode(func_t,allBlocks[item].startEA,allBlocks[item].endEA)
        binaryInBlock = getAllBinaryInstrInOneNode(func_t,item,startEnd[item])
        document = {}
        document["start"] = item
        document["end"]=startEnd[item]
        document["hexInstrs"]=binaryInBlock
        database.insertOneForBlock(db,document)
    document1List = []
    for item in reps:
        repBinary = getRepBinaryInstrInOneAddr(item,ItemSize(item))
        document1 = {}
        document1["start"] = item
        document1["hexInstrs"]=repBinary
        document1["end"] = 0#暂时不需要
        document1List.append(document1)
    print "reps",reps
    database.insertManyForBlock(db,document1List)
        #binaryInBlock=eval(binaryInBlock) ################### binaryInBlock 原来装的是“转义后字符串”。我们用 eval 把这个串当做 python 代码去解释，得到想要的串。
        #print "binaryInBlock:",type(binaryInBlock),len(binaryInBlock),binaryInBlock
        #convertToIR.constructIR(binaryInBlock, item)
    '''    
    result = database.findAllBlocks(db)
    for i in result:
        start = i["start"]
        instrs = i["hexInstrs"]
        print start
        print instrs
        print eval(instrs)
        #print "instrs:",type(instrs),instrs
        convertToIR.constructIR(eval(instrs), start)
    '''
    #print "<-----开始伪代码表示的函数参数----->"
    #print "function:",GetFunctionName(func_t.startEA)
    #registerParameterList = getRegisterParametersFromFunctionPseudocode(func_t.startEA) #由于MIPS平台没有伪代码生成模块，所以这种方法被摒弃了
    #print registerParameterList
    #print "<-----结束伪代码表示的函数参数----->"
    print "###############开始识别函数参数:",GetFunctionName(func_t.startEA)
    registerArgs = []
    functionSet.clear()
    print "befor calling identifyStackArgsForMIPS32"
    stackArgs = identifyStackArgsForMIPS32(func_t)
    print "befor calling identifyRegisterArgs"
    placeholder, registerArgs, modifiedArgs = identifyRegisterArgs(func_t)
    registerArgs = removeDollar(registerArgs)
    print "寄存器参数:",registerArgs
    print "栈参数:",stackArgs
    print "###############结束识别函数参数:",GetFunctionName(func_t.startEA)
    funDocument = {}
    funDocument["start"] = startAddr
    funDocument["end"] = func_t.endEA
    funDocument["stackArgs"] = list(stackArgs)
    funDocument["registerArgs"] = list(registerArgs)
    funDocument["name"] = str(GetFunctionName(startAddr))
    if functionEBPBased[str(GetFunctionName(startAddr))]:
        funDocument["ebpBased"] = 1
    else:
        funDocument["ebpBased"] = 0
    global isVulnerabilityProgram
    if isVulnerabilityProgram:
        funDocument["vulnerability"] = 0
        funDocument["cve-num"]=""
    if startAddr not in notDefinedFunctions:
        database.insertOneForFunction(db,funDocument)
        #identifyArgs(func_t)

def storeFunction(db,functionsDict):
    documents = []
    for key in functionsDict.keys():
        document = {}
        document["start"] = key
        document["name"] = functionsDict[key]
        documents.append(document)
    database.insertManyForLibFunction(db,documents)
        
#这个方法没有效果啊https://reverseengineering.stackexchange.com/questions/8870/extracting-arguments-from-ida
def getArgs(addr,name):
    tif = tinfo_t()
    print set_tinfo2(here(),tif)
    print get_tinfo2(here(),tif)
    funcdata =  func_type_data_t()
    print tif.get_func_details(funcdata)
    print funcdata.size()
    print "for function:",name
    for i in xrange(funcdata.size()):
        print "Arg %d: %s (of type %s, and of location: %s)" % (i, funcdata[i].name, print_tinfo('', 0, 0, PRTYPE_1LINE, funcdata[i].type, '', ''), funcdata[i].argloc.atype())

def generateRandomArgs(db,funName):
    randomValueList = randomInput.getRandomValueList()
    document = {}
    document["name"] = funName
    document["randomValues"] = randomValueList
    database.insertOneForRandomValue(db,document)

def getFunctions(db):
    functionList = []
    functionMap = {}
    num = 0
    global functionEBPBased
    for i in range(0,get_func_qty()):
        fun = getn_func(i) # get_func returns a func_t struct for the function
        segname = get_segm_name(fun.startEA) # get the segment name of the function by address ,x86 arch segment includes (_init _plt _plt_got _text extern _fini)
        funName = str(GetFunctionName(fun.startEA))
        function.lib_function[fun.startEA] = funName
        if segname[1:3] not in ["OA","OM","te"]:
            continue        
        if funName in globalVariable.addedFunctions:
            continue
        globalVariable.functionListStruct.append(fun)
        funcInstance = Process_with_Single_Function(fun)#为每一个函数生成一个instance对象，里面包含图关系，最终得到了函数的paths
        getAllPath(funcInstance)
        #name = str(GetFunctionName(fun.startEA))
        functionList.append(funName)
        function.functionMap[funName]=fun
        function.identifiedVisited[funName] = False
        function.identifiedVisited_stack[funName] = False
        func_flags = GetFunctionFlags(fun.startEA)
        generateRandomArgs(db,funName)
        if (func_flags & FUNC_FRAME):#is this an ebp-based frame?
            functionEBPBased[funName] = True
        else:
            functionEBPBased[funName] = False
        #getArgs(fun.startEA, funName)
    print "functionEBPBased:"
    print functionEBPBased
    print "libFunctions: ", function.lib_function
    storeFunction(db,function.lib_function)
    global f
    f.flush()
    return functionList,functionMap


def getFunctions_new(db):
    functionList = []
    functionMap = {}
    num = 0
    global functionEBPBased
    for i in range(0,get_func_qty()):
        fun = getn_func(i) # get_func returns a func_t struct for the function
        segname = get_segm_name(fun.startEA) # get the segment name of the function by address ,x86 arch segment includes (_init _plt _plt_got _text extern _fini)
        funName = str(GetFunctionName(fun.startEA))
        function.lib_function[fun.startEA] = funName
        if segname[1:3] not in ["OA","OM","te"]:
            continue        
        if funName in globalVariable.addedFunctions_mips32:
            continue
        globalVariable.functionListStruct.append(fun)
        #funcInstance = Process_with_Single_Function(fun)#为每一个函数生成一个instance对象，里面包含图关系，最终得到了函数的paths
        #getAllPath(funcInstance)
        #name = str(GetFunctionName(fun.startEA))
        functionList.append(funName)
        function.functionMap[funName]=fun
        function.identifiedVisited[funName] = False
        function.identifiedVisited_stack[funName] = False
        func_flags = GetFunctionFlags(fun.startEA)
        num = num + 1
        print "随机生成参数数量：",num 
        generateRandomArgs(db,funName)
        if (func_flags & FUNC_FRAME):#is this an ebp-based frame?
            functionEBPBased[funName] = True
        else:
            functionEBPBased[funName] = False
        getArgs(fun.startEA, funName)
    print "functionList",functionList
    print "functionEBPBased:"
    print functionEBPBased
    print "libFunctions: ", function.lib_function
    storeFunction(db,function.lib_function)
    global f
    f.flush()
    return functionList,functionMap

def findJumpTable():
    pass

def changeEncoding(value):
    encoding =  chardet.detect(value)
    print encoding
    type = encoding["encoding"]
    print type
    if type == "ISO-8859-1":
        value = value.decode("ISO-8859-1").encode("utf-8")
        print "convert encoding if"
        return value
    elif (type is None) or (type == "ISO-8859-8"):
        value = " "
        print "convert encoding elif",type
        return value
    else:
        value = value.decode(type.lower()).encode("utf-8")
        print "convert encoding else",chardet.detect(value)['encoding']
        return value

def storePushAndCall(db):
    
    global pushAndCallList
    tempList = list(pushAndCallList)
    print "pushAndCall",tempList
    document = {}
    document["addrs"] = tempList
    try:
        #pass
        database.insertAllForPushAndCall(db,document)
    except BaseException:
        global f
        f.close()


def storeConst(db):
    documents = []
    for key in segment.constUsage.keys():
        print "key",key
        document = {}
        value = segment.constUsage[key]
        #if value == '\xc8':
            #value = ''
        document["addr"] = key
        document["value"] = value
        print document
        try:
            database.insertOneForConst(db,document)
        except BaseException,e:
            print 'str(Exception):\t', str(Exception)
            print 'str(e):\t\t', str(e)
            print 'repr(e):\t', repr(e)
            print 'e.message:\t', e.message
            print 'traceback.print_exc():'; traceback.print_exc()
            print 'traceback.format_exc():\n%s' % traceback.format_exc()
            global f
            f.close()
        documents.append(document)
    print documents
    print "constUsage:"
    print segment.constUsage
    #database.insertManyForConst(db,documents)

def initSegment(db):
    result = Segments()#return the start address of each segment
    documents = []
    for startAddr in result:
        #print hex(startAddr)
        document = {}
        name = get_segm_name(startAddr)
        print "----start segment----"
        print name
        print "----end segment----"
        document["name"] = name[1:]
        document["start"] = startAddr
        document["end"] = SegEnd(startAddr)
        documents.append(document)
        #print name
        if name[1:]=="rodata":
            endAddr = SegEnd(startAddr)
            segment.rodataSegment.append(startAddr)
            segment.rodataSegment.append(endAddr)
        if name[1:]=="data":
            endAddr = SegEnd(startAddr)
            segment.dataSegment.append(startAddr)
            segment.dataSegment.append(endAddr)
    database.insertManyForSegment(db,documents)     


def createGraph(funcInstance):
    g = graph.Graph(funcInstance._num)
    g.add_nodes([i for i in range(funcInstance._num)])
    for m in funcInstance._offspringSet.keys():
        for n in funcInstance._offspringSet[m]:
            if m!=n:
                g.add_edge((funcInstance._mapping[m],funcInstance._mapping[n]))
                #print "edge:",funcInstance._mapping[m]," ---> ",funcInstance._mapping[n]
            else:
                print "自环边"    
    #print "nodes:",g.nodes()
    paths = []
    for item in funcInstance._endblocks:
        node = funcInstance._mapping[item]
        #path = g.getAllPaths2(0,node,funcInstance._name_func)
        path = g.getOnePath(0,node,funcInstance._name_func)
        #path = g.depth_first_search1(0,node)
        paths.extend(path)
        #break
    return paths

def getAllInstrAddrInOneBlock(func_t,startEA,endEA):
    #print "=======getAllAsmInstrInOneNode",startEA,"========="
    #instr_list = []
    it_code = func_item_iterator_t(func_t, startEA)
    ea = it_code.current() 
    address = []
    while (ea < endEA):
        #instr = get_instruction(ea)
        #instr_list.append(instr)
        address.append(ea)
        if(not it_code.next_code()):
            break
        ea = it_code.current()
    #print "instr:"
    #print instr_list
    return address
    
def getAllPath(funcInstance):
    global allFuncInstancesPath
    #if funcInstance._addr_func != 134689952:
        #return
    print "--------",funcInstance._name_func,"----"
    print "start block",funcInstance._addr_func," id:",funcInstance._mapping[funcInstance._addr_func]
    print "end blocks",funcInstance._endblocks
    for i in funcInstance._endblocks:
        print i,":",funcInstance._mapping[i]
    print "end size:",len(funcInstance._endblocks)
    print "addr:id",funcInstance._mapping
    print "successors",funcInstance._offspringSet    
    
    reverse_Id_Addr = dict((v,k) for k,v in funcInstance._mapping.iteritems())  
    allPaths = createGraph(funcInstance)
    print "allPaths:",len(allPaths),allPaths
    allPaths_addr = []
    for path in allPaths:
        path_addr = []
        for item in path:
            path_addr.append(reverse_Id_Addr[item])
        allPaths_addr.append(path_addr)
    print "allPaths_addr:",allPaths_addr
    allInstr = []
    for path in allPaths_addr:
        instr = []
        for item in path:
            value = getAllInstrAddrInOneBlock(funcInstance._func,item,funcInstance._block_boundary[item])
            instr.extend(value)
        allInstr.append(instr)
    print "allInstr:",allInstr
    funcInstance.allPaths = allInstr
    allFuncInstancesPath[funcInstance._addr_func] = funcInstance
    print "+++++++++++++++++++++++++++++++++++++++"

def print_help():
    help = 'args not enough'
    #print help
    
def printArgs(db):
    functionArgs = database.findAllFunctions(db)
    #print type(functionArgs),functionArgs
    
    for i in functionArgs:
        print "-----------------------------------------------"
        print "name:",i["name"]
        print "stackArgs:",i["stackArgs"]
        print "registerArgs:",i["registerArgs"]
        print "-----------------------------------------------"

def processSwitch(db,startAddr,endAddr):
    #stmtAddr是执行switch选择的jump语句的地址
    #jumpStart是jump table的起始地址，在rodata区
    #cases是0,1,2，。。。。等的case
    #target是跳转的目标地址
    stmtAddrList,jumpStartList,jumpEndList,casesList,targetsList = identify_switch(startAddr,endAddr)
    for i in range(len(stmtAddrList)):
        funcName = GetFunctionName(stmtAddrList[i])
        targets_sorted = sorted(targetsList[i])
        document = {}
        document["funcName"] = funcName
        document["funcStart"] = startAddr
        document["funcEnd"] = endAddr
        document["stmtAddr"] = stmtAddrList[i]
        document["jumpStartAddr"] = jumpStartList[i]
        document["jumpEndAddr"] = jumpEndList[i]
        document["firstTarget"] = targets_sorted[0]
        document["cases"] = casesList[i]
        document["targets"] = targetsList[i]
        database.insertOneForSwitch(db,document)
    

def dropCollections(db):
    db.function.drop()
    db.block.drop()
    db.const.drop()
    db.segment.drop()
    db.lib.drop()
    db.switch.drop()
    db.pushAndCall.drop()

def initialSameRandomValue(db):#需要确认仿真时用的是否是这个
    list1 = randomInput.getRandomValueList()
    document = {}
    document["name"] = "sameRandomValueList"
    document["valueList"] = list1
    database.insertOneForSameRandomValue(db,document)

def identifyConstsAgain(start,end):
    currentAddr = start
    while(currentAddr < end):
        disam = idc.GetDisasm(currentAddr)
        print "currentAddr:",hex(currentAddr),"disam:",disam,"size:", ItemSize(currentAddr)
        #currentAddr = NextAddr(currentAddr)
        size = ItemSize(currentAddr)
        value = "!@#$"
        if ".align" in disam:
            pass
        elif ".word" in disam:
            value = int(Dword(currentAddr))
        elif ".ascii" in disam:
            value = changeEncoding(GetString(currentAddr))
            #value = GetString(currentAddr)
            print "encoding",chardet.detect(value)['encoding']
            #value = value.replace("\xFF", "0xFF")
        elif size == 8:
            value = GetDouble(currentAddr)
        elif size == 4:
            if '.' in disam[1:]:
                value = round(GetFloat(currentAddr),6)
            else:
                value = int(Dword(currentAddr))
        elif size == 2:
            value = int(Dword(currentAddr))
        elif size == 1:
            value = Byte(currentAddr)
            print "value < 0",value < 0,"value > 255",value > 255
            if value < 0 or value > 255:
                value = 0
            print value, type(value)
        if value != "!@#$":
            print "    ",value
            segment.constUsage[currentAddr] = value
        else:
            print         
        currentAddr = currentAddr + ItemSize(currentAddr)


def parseArgs():
    print "idbPath:",GetIdbPath()
    print "inputFilePath:",GetInputFilePath()
    print "inputFile:",GetInputFile()
    global fileName,programName
    fileName = GetInputFile()
    programName = GetInputFilePath().split('\\')[-2]#项目名指openssl名字带有具体的版本号，文件名指项目下的具体文件的名字，如果是静态链接程序那么就可能是项目的名字，如果是动态链接文件，那么就是具体的库文件的名字
    #print "programName:",programName
    #print "fileName:",fileName   
    #print "idc args:",len(ARGV)
    argList = ARGV[1:]
    print "argList:",argList
    if len(argList) == 0:
        return
    for arg in argList:
        tempList = arg.split('=')
        if tempList[0]=="--type":
            if tempList[1] in ["V","v"]:
                global isVulnerabilityProgram
                isVulnerabilityProgram=True
                print "预处理的程序为漏洞程序"
            else:
                print "预处理的程序为目标程序"
        else:
            print "参数解析错误,参数使用为--type=T or --type=V"
            exit()
            
def main():
    #print "help"
    global is64bit_binary,isVulnerabilityProgram,programName,fileName
    is64bit_binary = GetIdbPath().endswith("i64") 
    loadDecompilePlugin()
    parseArgs()
    global f
    print_help()
    if len(idc.ARGV) < 0:
        print_help()
        return
    set_seg = set()
    #print "args;",idc.ARGV
    #print "args[0]",idc.ARGV[0]
    db,client = database.connectDB(isVulnerabilityProgram,False,programName,fileName)
    database.dropCollections(db)
    #dropCollections(db)
    initialSameRandomValue(db)
    initSegment(db)
    functionList = getFunctions_new(db)#all the functions in .text section except addedFunctions
    #print "functionList:",functionList
    
    for func in globalVariable.functionListStruct:#func is a struct describing functions
        processSwitch(db,func.startEA,func.endEA)
        processFunction(func,db)
        condition = {}
        condition["start"] = func.startEA
        #condition["name"] = str(GetFunctionName(func.startEA))
        database.findOneFunction(db,condition)
        f.flush()
        #get_All_instr_in_one_Node(func,func.startEA)
        #print "------------------start to calculate features for function:",funcInstance.getFuncName()
        #allnodes = funcInstance.getAll_Nodes_Addr()
        #features = funcInstance.calculateFeatures(allnodes)
        #functions_features[funcInstance.getFuncName()]= features
        #funcInstance.get_reference_data_one_block(allnodes[0])
    #traverseBlockInFunction(functions_features,functions_features)
    #writeBlockInfoToFile(functionMap,functions_features)
    #database.closeConnect()
    storePushAndCall(db)
    if len(segment.rodataSegment)!=0:
        identifyConstsAgain(segment.rodataSegment[0],segment.rodataSegment[1])
    if len(segment.dataSegment)!=0:
        identifyConstsAgain(segment.dataSegment[0],segment.dataSegment[0])
    storeConst(db)
    printArgs(db)    
    #print segment.constUsage
    database.closeConnect(client)
    client = None
    return

def load_plugin_decompiler():
    global is64bit_binary
    if is64bit_binary:
        #加载64位的插件
        RunPlugin("hexx64", 0)
    else:
        #加载32位的插件
        RunPlugin("hexrays", 0)
        RunPlugin("hexarm", 0)

def loadDecompilePlugin():
    global hasDecompiler
    if not init_hexrays_plugin():
        load_plugin_decompiler()
    if not init_hexrays_plugin():
        print "hexrays decompiler is not available :("
        hasDecompiler = False
        #raise Exception("hexrays decompiler is not available :(")

#redirect output into a file, original output is the console.
def stdout_to_file(output_file_name, output_dir=None):
    '''Set stdout to a file descriptor
    param: output_file_name: name of the file where standard output is written.
    param: output_dir: output directory for output file, default to script directory.
    Returns: output file descriptor, original stdout descriptor
    '''
    global f
    # obtain this script path and build output path
    if not output_dir:
        output_dir = os.path.dirname(os.path.realpath(__file__))

    output_file_path = os.path.join(output_dir, output_file_name)

    print "original output start"
    # save original stdout descriptor
    orig_stdout = sys.stdout

    # create output file
    f = file(output_file_path, "w")

    # set stdout to output file descriptor
    sys.stdout = f

    return f, orig_stdout

if __name__ == '__main__':
    global f
    # get original stdout and output file descriptor
    f, orig_stdout = stdout_to_file("output.txt")
    main()
    sys.stdout = orig_stdout #recover the output to the console window
    f.close()
    
    #idc.Exit(0)