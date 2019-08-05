import os
import glob
import numpy as np
import sys
import fileinput
import re
from collections import deque


# Check the source to get the tainted variable
def checkSrcVar(srcLocInfo, fileInfo, lineInfo):
    with open(srcLocInfo) as f:
        for idx, line in enumerate(f, 1):
            if idx < lineInfo:
                continue
            else:
                srcLine = line.strip()
                break

    # Heuristic check
    # Check if it matches any if statement and filter it out
    filterStr = re.search('if\s*\(.+\)', srcLine)
    if filterStr != None:
        filterStr = filterStr.group()
        srcLine = srcLine[len(filterStr):].strip()

    # Check for assignment symbol and extract the LHS
    if "++" in srcLine:
        LHS = srcLine[:srcLine.find("++")].strip()
    elif "--" in srcLine:
        LHS = srcLine[:srcLine.find("--")].strip()
    elif "+=" in srcLine:
        LHS = srcLine[:srcLine.find("+=")].strip()
    elif "-=" in srcLine:
        LHS = srcLine[:srcLine.find("-=")].strip()
    elif "*=" in srcLine:
        LHS = srcLine[:srcLine.find("*=")].strip()
    elif "\=" in srcLine:
        LHS = srcLine[:srcLine.find("/=")].strip()
    elif " = " in srcLine:
        LHS = srcLine[:srcLine.find(" = ")].strip()
    else:
        return None

    # Extract tainted variable
    variables = \
        re.findall(r'[_a-zA-Z]+[_a-zA-Z0-9]*|[_a-zA-Z]+[_a-zA-Z0-9]*\.[_a-zA-Z]+[_a-zA-Z0-9]', LHS)

    return variables[0]

def get_data(srcDir,log):
    # array to store all lines
    data = []
    f = []
    with open(srcDir+log) as logfile:
        for line in logfile:
            f.append(line)

    # Pass 1: Remove non-taintgrind output
    for i in range(len(f)):
        line = f[i]

        if not line.startswith("0x"):
            continue

        # Need to remove valgrind warnings, which add a LF
        # We need to add the next line as well
        if "-- warning:" in line:
            elts = line.split("|")
            nextline = f[i + 1]
            c = 2

            while "-- warning:" in nextline:
                nextline = f[i + c]
                c += 1

            elts[-1] = " " + nextline
            line = "|".join(elts)

        data.append(line)

    return data

def get_loc(line):
    if '(' in line.split()[1]:
        return line.split()[1].split('(')[0]
    return line.split()[1] 

def get_source(line):
    tmp1=line.split('(')
    tmp2=tmp1[1].split(')')[0]
    tmp3=tmp2.split(':')
    return tmp3[0],tmp3[1]

def sanitise_var(varname,addr,srcDict,unknownobjdict):
    # dot will complain if we have strange chars
    varname = varname.replace('[','_').replace(']','_')
    varname = varname.replace('.','_').replace('.','_')
    srcfile,linenum=get_source(addr)
    tmp1=[]
    tmp2=False
    
    # E.g. <address>_unknownobj -> a<address>
    if "_unknownobj" in varname:
        tmp00=srcfile+'|'+linenum+'|'+'a' + varname.split("_unknownobj")[0]
        tmp0='a' + varname.split("_unknownobj")[0]
        if tmp00 in unknownobjdict:
            varname2=unknownobjdict[tmp00]
        else:
            varname2=tmp0
                
        tmp1=[varname2,varname2]
        tmp2=True
                
        varname=tmp0

    # E.g. <varname>:<address> -> a<address>
    if ":" in varname:
        tmp1=varname.split(":")
        tmp2=True
        varname = 'a' + tmp1[1]

    # dot will complain if var name starts with a number
    if re.match('^[0-9]',varname):
        varname = 'g' + varname

    # dot will complain if var name contains a space
    if ' ' in varname:
        varname = varname.split(' ')[0]
    
    varname=varname+'|'+re.sub(' ','',addr.split(': ')[1])
    
    if tmp2:
         varname = varname + '|' + tmp1[0]
    
    return "\""+varname+"\""

def get_graph(data,srcDict,unknownobjdict):
    edges = []
    nodes = {}


    for line in data:
        addr = ""
        insn = ""
        insnty = ""
        val = ""
        flow = ""


        a = line.rstrip().split(" | ")

        if len(a) == 5:
            (addr,insn,insnty,val,flow) = line.rstrip().split(" | ")
        elif len(a) == 4:
            (addr,insnty,val,flow) = line.rstrip().split(" | ")
        elif len(a) == 2:
            (addr,flow) = line.rstrip().split(" | ")
        else:
            print "%d" % (len(a))
            sys.exit(0)
            
        # If there is taint flow
        if len(flow) >= 4:
            # Get location/function of line
            loc = get_loc(line)

            if " <- " in flow:
                (sink,sources) = flow.split(" <- ")

                for source in sources.split():
                    # Add an edge for each source
                    if "(" not in source:
                        varname=sanitise_var(source,addr,srcDict,unknownobjdict)
                        # Direct source
                        edges.append("%s -> %s" % (varname,sanitise_var(sink,addr,srcDict,unknownobjdict)))
                        if varname not in nodes:
                            tmp=checkinsrc(srcDict,varname)
                            if tmp!=None:
                                nodes[varname] = ("%s [label=\"%s\"]" % (varname, tmp), loc)
                            else:
                                nodes[varname] = ("%s [label=\"\" shape=point]" % (varname), loc)
                                
                    else:
                        # Indirect source, colour it red
                        source2 = source[1:-1]
                        varname=sanitise_var(source2,addr,srcDict,unknownobjdict)
                        edges.append("%s -> %s[color=\"red\"]" % (varname,sanitise_var(sink,addr,srcDict,unknownobjdict)))
                        if varname not in nodes:
                            tmp=checkinsrc(srcDict,varname)
                            if tmp!=None:
                                nodes[varname] = ("%s [label=\"%s\"]" % (varname, tmp), loc)
                            else:
                                nodes[varname] = ("%s [label=\"\" shape=point]" % (varname), loc)

                vname = sanitise_var(sink,addr,srcDict,unknownobjdict)

                if (len(sources.split()) > 1) and ("Load" in insnty or "Store" in insnty):
                    # If both address and data to this Load/Store are tainted,
                    # Colour it red
                    tmp=checkinsrc(srcDict,vname)
                    if tmp!=None:
                        nodes[vname] = ("%s [label=\"%s\",fillcolor=red,style=filled]" % (vname, tmp), loc)
                    else:
                        nodes[vname] = ("%s [label=\"\" shape=point]" % (vname), loc)
                elif val and insnty:
                    tmp=checkinsrc(srcDict,vname)
                    if tmp!=None:
                        nodes[vname] = ("%s [label=\"%s\"]" % (vname, tmp), loc)
                    else:
                        nodes[vname] = ("%s [label=\"\" shape=point]" % (vname), loc)
                else:
                    nodes[vname] = ("%s [label=\"\" shape=point]" % (vname), loc)

            elif "Jmp" in insnty:
                vname = sanitise_var(flow,addr,srcDict,unknownobjdict)
                # If jump target is tainted, colour it red
                tmp=checkinsrc(srcDict,vname)
                if tmp!=None:
                    nodes[vname] = ("%s [label=\"%s\",fillcolor=red,style=filled]" % (vname, tmp), loc)
                else:
                    nodes[vname] = ("%s [label=\"\" shape=point]" % (vname), loc)
            elif val and insnty:
                vname = sanitise_var(flow,addr,srcDict,unknownobjdict)
                tmp=checkinsrc(srcDict,vname)
                if tmp!=None:
                    nodes[vname] = ("%s [label=\"%s\"]" % (vname, tmp), loc)
                else:
                    nodes[vname] = ("%s [label=\"\" shape=point]" % (vname), loc)
            else:
                vname = sanitise_var(flow,addr,srcDict,unknownobjdict)
                nodes[vname] = ("%s [label=\"\" shape=point]" % (vname), loc)
    return edges,nodes

def get_srcDict(srcDir):
    # src directory dict
    srcDict = dict()
    # create edges in order

    srcFiles = glob.glob(srcDir + "*.c")
    for sf in srcFiles:
        d, f = os.path.split(sf)
        srcDict[f] = sf
    
    return srcDict
        
def print_graph_verbose(data,nodes,edges,srcDict):
    subgraph = {}
    for line in data:
        addr = ""
        insn = ""
        insnty = ""
        val = ""
        flow = ""



        a = line.rstrip().split(" | ")

        if len(a) == 5:
            (addr,_,_,_,flow) = line.rstrip().split(" | ")
        elif len(a) == 4:
            (addr,_,_,flow) = line.rstrip().split(" | ")
        elif len(a) == 2:
            (addr,flow) = line.rstrip().split(" | ")
        else:
            print "%d" % (len(a))
            sys.exit(0)

        # If there is taint flow
        if len(flow) >= 4:
            # Get location/function of line
            loc = get_loc(line)

            if " <- " in flow:
                (sink,sources) = flow.split(" <- ")

                for source in sources.split():
                    # Add an edge for each source
                    if "(" not in source:
                        # Direct source
                        varname=sanitise_var(source,addr,srcDict,False)
                        subgraph = add_node(subgraph, nodes[varname][0], nodes[varname][1])
                    else:
                        # Indirect source, colour it red
                        source2 = source[1:-1]
                        varname=sanitise_var(source2,addr,srcDict,False)
                        subgraph = add_node(subgraph, nodes[varname][0], nodes[varname][1])
                
                varname = sanitise_var(sink,addr,srcDict,True)
                subgraph = add_node(subgraph, nodes[varname][0], nodes[varname][1])
            else:
                varname=sanitise_var(flow,addr,srcDict,False)
                subgraph = add_node(subgraph, nodes[varname][0], nodes[varname][1])



    # Now we construct the graph
    print "digraph {"


    # Print subgraphs
    for s in subgraph:
        print "    subgraph cluster_%s{" % (s.replace(":","_").replace("???","unknown"))
        print "        label=\"%s\"" % (s)
        print subgraph[s]
        print "    }"

    # Print the edges
    for e in edges:
        print "    " + e

    print "}"
    
def add_node(g, label, loc):
    if loc not in g:
        g[loc] = ""
    elif label not in g[loc]:
        g[loc] += "    %s\n" % (label)

    return g

def create_neiborlist(edges,nodes):
    # nodedict=dict()
    # count=0
    # neiborlist=[]
    # r_nodedict2=dict()
    # nodedict2=dict()
    # for i in nodes.keys():
    #     tmpsplit=i.split('|')
    #     tmpvarname=re.sub('"','',tmpsplit[0].strip())
    #     if tmpvarname not in nodedict:
    #         nodedict[tmpvarname]=count
    #         count=count+1
    #     nodedict2[i]=count
    #     if count not in r_nodedict2:
    #         r_nodedict2[count]=[]
    #     r_nodedict2[count].append(i)
        
    # newedges=[]
    # for i in range(count):
    #     neiborlist.append([])
    # for ii in edges:
    #     i=ii
    #     if "[color=\"red\"]" in ii:
    #         i=ii.split("[color=\"red\"]")[0]
    #     tmp1=i.split('->')
    #     var1=re.sub('"','',tmp1[0].split('|')[0].strip())
    #     var2=re.sub('"','',tmp1[1].split('|')[0].strip())
    #     node1=nodedict[var1.strip()]
    #     node2=nodedict[var2.strip()]
        
    #     neiborlist[node1].append(node2)
    
    # return neiborlist,nodedict,r_nodedict2,nodedict2
    #neiborlist,nodedict,r_nodedict2,nodedict2=create_neiborlist(edges,nodes)
    nodedict=dict()
    count=0
    neiborlist=[]
    r_nodedict2=dict()
    nodedict2=dict()
    tmpdict=dict()
    for i in nodes.keys():
        tmpsplit=i.split('|')
        tmpvarname=re.sub('"','',tmpsplit[0].rstrip())
        if tmpvarname not in tmpdict:
            tmpdict[tmpvarname]=[]
        tmpdict[tmpvarname].append(i)

    for tmpvarname in tmpdict.keys():
        nodenamelist=tmpdict[tmpvarname]
        tmpcount=count+0
        if tmpvarname not in nodedict:
            nodedict[tmpvarname]=count
            count=count+1
            
        for i in nodenamelist:
            nodedict2[i]=tmpcount
        if tmpcount not in r_nodedict2:
            r_nodedict2[tmpcount]=[]
        r_nodedict2[tmpcount]=r_nodedict2[tmpcount]+nodenamelist

    newedges=[]
    for i in range(count):
        neiborlist.append([])
    for ii in edges:
        i=ii
        if "[color=\"red\"]" in ii:
            i=ii.split("[color=\"red\"]")[0]
        tmp1=i.split('->')
        var1=re.sub('"','',tmp1[0].split('|')[0].strip())
        var2=re.sub('"','',tmp1[1].split('|')[0].strip())
        node1=nodedict[var1.strip()]
        node2=nodedict[var2.strip()]
        neiborlist[node1].append(node2)
    
    return neiborlist,nodedict,nodedict2,r_nodedict2
    
def checkinsrc(srcDict,varname):
    tmp=varname.split("\"")[0]
    tmp2=tmp.split("|")
    if len(tmp2)>2:
        if tmp2[1] in srcDict:
            return tmp2[2]
        else:
            return None

def BFS(srcDict,neiborlist,taintednode,nodedict,r_nodedict2,nodedict2):
    # vardict=dict()
    # beginnode=[]
    # varnode=[]
    # vargraph=[]
    # vargraph2=[]
    
    # for i in nodedict2.keys():
    #     tmp=i.split('|')
    #     if len(tmp)>2:
    #         tmp2=tmp[1]+'|'+tmp[2].split('\"')[0].strip()
    #         if tmp2 in taintednode:
    #             beginnode.append(nodedict2[i])
    #         varnode.append(nodedict2[i])
    
    # beginnode=set(beginnode)
    # varnode=set(varnode)
    
    # count=0;
    
    # for i in beginnode:
    #     varn='\"'
    #     for j in r_nodedict2[i]:
    #         varn=varn+j[i].split('|')[1].split('\"')[0]+j[i].split('|')[2].split('\"')[0]+'\n'
    #     varn=varn+'\"'
    #     vargraph2.append(varn+"[fillcolor=darkslategray1,style=filled]")
    #     count=count+1
    
    # search_queue=deque()
    # for i in beginnode:
    #     tmp_var_node=[]
    #     for j in varnode:
    #         tmp_var_node.append(j)
    #     search_queue.append([i,0,i])
    #     # 0: curr unfolede node, 1: distance to nearest var node
    #     # 2: nearest var node
    #     searched = []
    #     tmp_var_node.remove(i)
    #     while search_queue and len(tmp_var_node)>0:
    #         currnode = search_queue.popleft()
    #         if not currnode[0] in searched:
    #             searched.append(currnode[0])
    #             if currnode[0] in tmp_var_node:
    #                 vargraph.append([currnode[2],currnode[1],currnode[0]])
    #                 tmp_var_node.remove(currnode[0])
    #                 for j in neiborlist[currnode[0]]:
    #                     search_queue.append([j,1,currnode[0]])
    #             else:
    #                 for j in neiborlist[currnode[0]]:
    #                     search_queue.append([j,currnode[1]+1,currnode[2]])
    
    
    # for i in vargraph:
    #     if i[1]==0:
    #         continue
    #     node1=i[0]
    #     node2=i[2]
    #     var1='\"'
    #     for j in r_nodedict2[node1]:
    #         var1=var1+j[i].split('|')[1].split('\"')[0]+j[i].split('|')[2].split('\"')[0]+'\n'
    #     var1=var1+'\"'
    #     var2='\"'
    #     for j in r_nodedict2[node2]:
    #         var2=var2+j[i].split('|')[1].split('\"')[0]+j[i].split('|')[2].split('\"')[0]+'\n'
    #     var2=var2+'\"'
    #     vargraph2.append(var1+'->'+var2+"[label=\"%s\"]" % str(i[1]))
            
    # return vargraph2
    vardict=dict()
    beginnode=[]
    varnode=[]
    vargraph=[]
    vargraph2=[]

    for i in nodedict2.keys():
        tmp=i.split('|')
        if len(tmp)>2:
            tmp2=tmp[1]+'|'+tmp[2].split('\"')[0].rstrip()
            if tmp2.rstrip() in taintednode:
                beginnode.append(nodedict2[i])
                varnode.append(nodedict2[i])
            elif tmp[1].split('(')[1].split(':')[0] in srcDict and re.sub('\"','',tmp[0])!=re.sub('\"','',tmp[2]):
                varnode.append(nodedict2[i])

    beginnode=set(beginnode)
    varnode=set(varnode)

    count=0;

    for i in beginnode:
        varn='\"'
        nameset=get_nameset(r_nodedict2[i])
        for j in nameset:
            varn=varn+re.sub('"','',j)+';'
        varn=varn+'\"'
        vargraph2.append(varn+"[fillcolor=darkslategray1,style=filled]")
        count=count+1
    
    search_queue=deque()
    for i in beginnode:
        tmp_var_node=set()
        for j in varnode:
            tmp_var_node.add(j)
        search_queue.append([i,0,i])
        # 0: curr unfolded node, 1: distance to nearest var node
        # 2: nearest var node
        searched = set()
        tmp_var_node.remove(i)
        while search_queue and len(tmp_var_node)>0:
            currnode = search_queue.popleft()
            if not currnode[0] in searched:
                searched.add(currnode[0])
                if currnode[0] in tmp_var_node:
                    vargraph.append([currnode[2],currnode[1],currnode[0]])
                    tmp_var_node.remove(currnode[0])
                    for j in neiborlist[currnode[0]]:
                        search_queue.append([j,1,currnode[0]])
                else:
                    for j in neiborlist[currnode[0]]:
                        search_queue.append([j,currnode[1]+1,currnode[2]])

    for i in vargraph:
        if i[1]==0:
            continue
        node1=i[0]
        node2=i[2]
        var1='\"'
        nameset=get_nameset(r_nodedict2[node1])
        for j in nameset:
            var1=var1+re.sub('"','',j)+';'
        var1=var1+'\"'
        var2='\"'
        nameset=get_nameset(r_nodedict2[node2])
        for j in nameset:
            var2=var2+re.sub('"','',j)+';'
        var2=var2+'\"'
        vargraph2.append(var1+'->'+var2+"[label=\"%s\"]" % str(i[1]))
    for i in range(len(vargraph2)):
        tmp0=vargraph2[i]
        tmp1=re.sub('a[0-9a-f]+\|','',tmp0)
        tmp2=re.sub(':[0-9]+\)',')',tmp1)
        vargraph2[i]=tmp2            

    vargraph3=dict()
    for i in vargraph2:
        vargraph3[re.sub("\[label=\"[0-9]+\"\]",'',i)]=float('inf')

    for i in vargraph2:
        tmp=re.sub("\[label=\"[0-9]+\"\]",'',i)
        if tmp in vargraph3:
            tmp1=re.findall("\[label=\"[0-9]+\"\]",i)
            if len(tmp1) > 0 :
                distance=int(re.findall('[0-9]+',tmp1[0])[0])
                if distance<vargraph3[tmp]:
                    vargraph3[tmp]=distance
    
    vargraph4=[]
    for i in vargraph3.keys():
        result=re.sub(';','\n',i)
        if vargraph3[i] < float('inf'):
            result=result+"[label=\"%d\"]"%vargraph3[i]

        vargraph4.append(result)
    
    return vargraph,vargraph2,vargraph3,vargraph4

def print_graph(vargraph):
    print "digraph {"
    for i in vargraph:
        print i.replace("\n","\\n")
    print "}"
    return 0
    
def get_unknownobjdict(data,srcDict):
    unknownobjdict=dict()
    for line in data:
        addr = ""
        insn = ""
        insnty = ""
        val = ""
        flow = ""
    

        a = line.rstrip().split(" | ")

        if len(a) == 5:
            (addr,insn,insnty,val,flow) = line.rstrip().split(" | ")
        elif len(a) == 4:
            (addr,insnty,val,flow) = line.rstrip().split(" | ")
        elif len(a) == 2:
            (addr,flow) = line.rstrip().split(" | ")
        else:
            print "%d" % (len(a))
            sys.exit(0)
            
        # If there is taint flow
        if len(flow) >= 4:
            # Get location/function of line
            loc = get_loc(line)

            if " <- " in flow:
                (sink,sources) = flow.split(" <- ")
                sinknamepair=get_unknownobjdict_sub(sink,addr,srcDict)
                if sinknamepair[0]!=None and sinknamepair[1]!=None:
                    if sinknamepair[0] not in unknownobjdict:
                        unknownobjdict[sinknamepair[0]]=sinknamepair[1]
                
    return unknownobjdict

def get_unknownobjdict_sub(varname,addr,srcDict):
    varname = varname.replace('[','_').replace(']','_')
    varname = varname.replace('.','_').replace('.','_')
    srcfile,linenum=get_source(addr)
    varname2=None
    tmp0=None
    
    if "_unknownobj" in varname:
        tmp0=srcfile+'|'+linenum+'|'+'a' + varname.split("_unknownobj")[0]
        if srcfile in srcDict:
            varname2 = checkSrcVar(srcDict[srcfile],srcfile,int(linenum))
    
    return [tmp0,varname2]

def get_nameset(rr): 
    flag=False
    nameset=[]
    for j in rr:
        if len(re.findall('\|a[0-9a-f]+',j))==0:
            flag=True
            tmp=j.split('|')[1]
            flag2=False
            for k in nameset:
                if re.sub(':[0-9]+\)','',tmp) in k:
                    flag2=True
            if flag2==False:
                nameset.append(j)
    if flag==False:
        nameset=rr
    
    return nameset

def main():
    f=open("config_info.txt")
    tmp=f.readlines()
    srcDir=''
    vgname=''
    taintednode=[]
    verboselevel=0
    try:
        srcDir=tmp[0].strip()
        vgname=tmp[1].strip()
        taintednode=tmp[2].strip().split(',')
        verboselevel=int(tmp[3].strip())
    except:
        print "Error configfile:"
        print "Line 1: source directory path"
        print "Line 2: .vg file path"
        print "Line 3: tainted nodes name, delimitered with \',\'"
        print "Line 4: output verbose level: 0~3"
        print "Tainted nodes name should be \'function_name(source_code_file_name:line_number)|variable_name_or_a_plus_address \'"
        return 
    srcDict=get_srcDict(srcDir)
    data=get_data(srcDir,vgname)
    unknownobjdict=get_unknownobjdict(data,srcDict)
    edges,nodes=get_graph(data,srcDict,unknownobjdict)
    neiborlist,nodedict,nodedict2,r_nodedict2=create_neiborlist(edges,nodes)
    vargraph1,vargraph2,vargraph3,vargraph4=BFS(srcDict,neiborlist,taintednode,nodedict,r_nodedict2,nodedict2)
    if verboselevel==0:
        print_graph(vargraph4)
    elif verboselevel==1:
        print_graph(vargraph3)
    elif verboselevel==2:
        print_graph(vargraph2)
    elif verboselevel==3:
        print_graph(vargraph1)

if __name__ == '__main__':
    main()