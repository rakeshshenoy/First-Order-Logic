import sys
import copy

def writeToFile(line):
    output = open('output.txt', 'a')
    output.write(str(line))
    output.close()

def addUnderscore(goal, theta):
    argList = goal[goal.find('(')+1:goal.find(')')].split(', ')
    newArgs = []
    for arg in argList:
            if(arg[0].islower()):
                if(arg in theta):
                    newArg = theta[arg]
                    while(newArg[0].islower() and newArg in theta):
                        newArg = theta[newArg]
                    newArgs.append(newArg)
                else:
                    newArgs.append('_')
            else:
                newArgs.append(arg)
    return goal[:goal.find('(')+1] + ', '.join(newArgs) + ')'

def replaceFromTheta(goal, theta):
    argList = goal[goal.find('(')+1:goal.find(')')].split(', ')
    newArgs = []
    for arg in argList:
        if(arg[0].islower() and arg in theta):
            newArg = theta[arg]
            while(newArg[0].islower() and newArg in theta):
                newArg = theta[newArg]
            newArgs.append(newArg)
        else:
            newArgs.append(arg)
    return goal[:goal.find('(')+1] + ', '.join(newArgs) + ')'

def getFirstRest(goals):
    return goals.partition(' && ')[0], goals.partition(' && ')[2]

def split_LHS_RHS(rule):
    lhs, rhs = '', ''
    if(' => ' in rule):
        lhs = rule.split(' => ')[0]
        rhs = rule.split(' => ')[1]
    else:
        rhs = rule
    return lhs, rhs

def unify_var(var, x, theta):
    theta = copy.deepcopy(theta)
    if(var in theta):
        return unify(theta[var], x, theta)
    elif (x in theta):
        return unify(var, theta[x], theta)
    else:
        theta[var] = x
        return theta
    
def unify(x, y, theta):
    theta = copy.deepcopy(theta)
    if theta == 'failure':
        return 'failure'
    elif x == y:
        return theta
    elif '(' not in x and ',' not in x and x[0].islower():
        return unify_var(x, y, theta)
    elif '(' not in y and ',' not in y and y[0].islower():
        return unify_var(y, x, theta)
    elif '(' in x and '(' in y:
        return unify(x.split('(')[1].split(')')[0], y.split('(')[1].split(')')[0], unify(x.split('(')[0], y.split('(')[0], theta))
    elif ',' in x and ',' in y:
        return unify(x.partition(', ')[2], y.partition(', ')[2], unify(x.partition(', ')[0], y.partition(', ')[0], theta))
    else:
        return 'failure'    
  
def standardize(rule, stdCount):
    ruleIndices = [i for i, letter in enumerate(rule) if letter == '(']
    for index in ruleIndices:
        if(rule[index + 1].islower()):
            rule = rule[:index + 2] + str(stdCount) + rule[index + 2:]
            ruleIndices[ruleIndices.index(index) + 1:] = [a + len(str(stdCount)) for a in ruleIndices[ruleIndices.index(index) + 1:]]
            
    ruleIndices = [i for i, letter in enumerate(rule) if letter == ',']
    for index in ruleIndices:
        if(rule[index + 2].islower()):
            rule = rule[:index + 3] + str(stdCount) + rule[index + 3:]
            ruleIndices[ruleIndices.index(index) + 1:] = [a + len(str(stdCount)) for a in ruleIndices[ruleIndices.index(index) + 1:]]

    return rule

def subst(theta, first):
    argList = first[first.find('(')+1:first.find(')')].split(', ')
    newArgs = []
    for arg in argList:
        if (arg[0].islower() and arg in theta):
            newArgs.append(theta[arg])
        else:
            newArgs.append(arg)
    return first[0:first.find('(')+1] + ', '.join(newArgs) + ')'

def fetch_rules_for_goal(KB, goal):
    clauses = []
    for clause in KB:
        if(' => ' in clause):
            if((clause.split(' => ')[1]).startswith(goal.partition('(')[0])):
                clauses.append(clause)
        else:
            if(clause.startswith(goal.partition('(')[0])):
                clauses.append(clause)
    return clauses

def fol_bc_and(KB, goals, rhs, theta):
    if(theta == 'failure'):
        return
    elif(len(goals) == 0):
        #print('True: ' + replaceFromTheta(rhs, theta))
        writeToFile('True: ' + replaceFromTheta(rhs, theta) + '\n')
        yield theta
    else:
        first, rest = getFirstRest(goals)
        for theta1 in fol_bc_or(KB, subst(theta, first), theta):
            for theta2 in fol_bc_and(KB, rest, rhs, theta1):
                yield theta2

def fol_bc_or(KB, goal, theta):
    global askedList, stdCount
    count = 0
    flag = False
    rulesList = fetch_rules_for_goal(KB, goal)
    for rule in rulesList:
        count = count + 1
        nextToAsk = addUnderscore(goal, theta)
        lhs, rhs = split_LHS_RHS(rule)

        if not askedList:
            writeToFile('Ask: '+ nextToAsk + '\n')
            askedList.append('Ask: ' + nextToAsk)
        elif askedList[-1] != nextToAsk:
            if nextToAsk in askedList:
                lhs, rhs = split_LHS_RHS(rule)
                if unify(rhs, goal, theta) != 'failure':
                    writeToFile('Ask: '+ nextToAsk + '\n')
                    askedList.append(nextToAsk)
            else:
                writeToFile('Ask: '+ nextToAsk + '\n')
                askedList.append(nextToAsk)
                
        rule = standardize(rule, stdCount)
        stdCount = stdCount + 1
        lhs, rhs = split_LHS_RHS(rule)
        
        for theta1 in fol_bc_and(KB, lhs, rhs, unify(rhs, goal, theta)):
            flag = True
            yield theta1
            
        if(count == len(rulesList) and flag == False):
            #print('False: ' + nextToAsk)
            writeToFile('False: ' + nextToAsk + '\n')

def fol_bc_ask(KB, query):
    theta = {}
    return fol_bc_or(KB, query, theta)

input = open(sys.argv[-1], "r").read().splitlines()
queryList = input[0].split(' && ')
KB = input[2:]
stdCount = 0
askedList = []
result = True
output = open('output.txt', 'w+')
output.close()
for query in queryList:
    askedList = []
    y = fol_bc_ask(KB, query)
    try:
        theta = next(y)
        result = True
    except StopIteration:
        result = False
writeToFile(result)