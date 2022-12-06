#ifndef __PROGTEST__

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <variant>
#include <vector>

using State = unsigned int;
using Symbol = uint8_t;

struct NFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, std::set<State>> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

struct DFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, State> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;
};

#endif

NFA total(const NFA& a) {
    NFA result;
    result.m_InitialState = a.m_InitialState;
    result.m_FinalStates = a.m_FinalStates;
    result.m_Alphabet = a.m_Alphabet;
    result.m_States = a.m_States;
    result.m_States.insert(1000);
    for(const auto& x: result.m_Alphabet)
        result.m_Transitions[{1000, x}].insert(1000);
    for(const auto& state: a.m_States){
        for(const auto& alfa: a.m_Alphabet){
            std::pair<State, Symbol> key = {state, alfa};
            if (a.m_Transitions.find(key) == a.m_Transitions.end())
                result.m_Transitions[key].insert(1000);
            else
                result.m_Transitions[key] = a.m_Transitions.at(key);
        }
    }
    return result;
}

void addState(std::map<std::pair<State, State>, State>& table, int& count, NFA& result, State aState, State bState){
    result.m_States.insert(count);
    table.insert({{aState, bState}, count});
    count++;
}

void finalUnify(const NFA& a, const NFA& b, State aState, State bState, NFA& result, State table){
    if(a.m_FinalStates.find(aState) != a.m_FinalStates.end() ||
       b.m_FinalStates.find(bState) != b.m_FinalStates.end())
        result.m_FinalStates.insert(table);
}

void finalIntersect(const NFA& a, const NFA& b, State aState, State bState, NFA& result, State table){
    if(a.m_FinalStates.find(aState) != a.m_FinalStates.end() &&
       b.m_FinalStates.find(bState) != b.m_FinalStates.end())
        result.m_FinalStates.insert(table);
}

NFA paralelRun(const NFA& a, const NFA& b, void (*func) (const NFA&, const NFA&, State, State, NFA&, State)){
    NFA result;
    std::set<Symbol> alfa = a.m_Alphabet;
    if(a.m_Alphabet.size() < b.m_Alphabet.size()){
        alfa.clear();
        alfa = b.m_Alphabet;
    }
    result.m_Alphabet = alfa;
    std::map<std::pair<State, State>, State> table;
    int count = 0;
    for(const auto& aState: a.m_States){
        for(const auto& bState: b.m_States){
            if(table.find({aState, bState}) == table.end())
                addState(table, count, result, aState, bState);
            //check initial State
            if(aState == a.m_InitialState && bState == b.m_InitialState)
                result.m_InitialState = table[{aState, bState}];
            func(a, b, aState, bState, result, table[{aState, bState}]);
            for(const auto& symbol: alfa){
                //get together set of Transitions, not work without total
                for(const auto& aSet: a.m_Transitions.at({aState, symbol})){
                    for(const auto& bSet: b.m_Transitions.at({bState, symbol})){
                        if(table.find({aSet, bSet}) == table.end())
                            addState(table, count, result, aSet, bSet);
                        result.m_Transitions[{table[{aState, bState}], symbol}].insert(table[{aSet, bSet}]);
                    }
                }
            }
        }
    }
    return result;
}

void addNewState(std::set<State>& newState, std::map<State,std::set<State>>& table,
                 std::map<std::set<State>, State>& used, int& count, std::queue<State>& added){
    if(!used.contains(newState)){
        added.push(count);
        table.insert({count, {newState}});
        used.insert({newState, count++});
    }
}

void deterFinal(std::set<State>& newState, const NFA& a, DFA& result, std::map<std::set<State>, State>& used){
    for(const auto& state: newState){
        if(a.m_FinalStates.contains(state)){
            result.m_FinalStates.insert(used.at(newState));
            return;
        }
    }
}

DFA determinization(const NFA& a){
    DFA result;
    result.m_Alphabet = a.m_Alphabet;
    result.m_InitialState = a.m_InitialState;

    int count = 0;
    State actual;
    std::map<State, std::set<State>> table;
    std::map<std::set<State>, State> used;
    std::queue<State> added;
    added.push(0);
    table.insert({ count, {a.m_InitialState}});
    used.insert({{a.m_InitialState}, count++});
    while(!added.empty()){
        actual = added.front();
        added.pop();

        for(const auto& alfa: a.m_Alphabet){
            std::set<State> newState;
            for(const auto& state: table[actual]){
                for(const auto& trans: a.m_Transitions.at({state, alfa})){
                    newState.insert(trans);
                }
            }
            addNewState(newState, table, used, count, added);
            result.m_Transitions.insert({{actual, alfa}, used.at(newState)});
            deterFinal(newState, a, result, used);
        }
    }
    return result;
}

void trim(DFA &a){
    DFA tmp;
    std::queue<State> states;
    std::set<State> added;

    tmp.m_InitialState = a.m_InitialState;
    tmp.m_Alphabet = a.m_Alphabet;
    tmp.m_States = a.m_States;
    states.push(a.m_InitialState);
    added.insert(a.m_InitialState);
    while(!states.empty()){
        for(const auto& alfa: a.m_Alphabet){
            State actual = a.m_Transitions.at({states.front(), alfa});
            if(!added.contains(actual)) {
                added.insert(actual);
                states.push(actual);
            }
            tmp.m_Transitions.insert({{states.front(), alfa}, actual});
            if(a.m_FinalStates.contains(actual))
                tmp.m_FinalStates.insert(actual);
        }
        states.pop();
    }
    added.clear();

    bool addState;
    a.m_Transitions.clear();
    for(const auto& end: tmp.m_FinalStates)
        added.insert(end);
    do{
        addState = false;
        for(const auto& tran: tmp.m_Transitions){
            if(added.contains(tran.second) && !added.contains(tran.first.first)){
                added.insert(tran.first.first);
                addState = true;
            }
        }
    } while(addState);
    a.m_States = added;
    for(const auto& tran: tmp.m_Transitions){
        if(added.contains(tran.second) && added.contains(tran.first.first))
            a.m_Transitions.insert(tran);
    }
}

bool compareState(const DFA &a, const std::map<State, State>& rename, const State& pattern, const State& state) {
    bool ok;
    for (const auto &alfa: a.m_Alphabet) {
        ok = false;
        if (!a.m_Transitions.contains({pattern, alfa})) {
            if (a.m_Transitions.contains({state, alfa}))
                return false;
            else
                ok = true;
        }
        if (!ok) {
            if (!a.m_Transitions.contains({state, alfa}))
                return false;
            if (rename.at(a.m_Transitions.at({pattern, alfa})) != rename.at(a.m_Transitions.at({state, alfa})))
                return false;
        }
    }
    return true;
}

void minimalize(DFA &a){
    std::map<State, State> rename;
    std::map<State, std::set<State>> groups;
    for(const auto& state: a.m_States){
        if(a.m_FinalStates.contains(state)){
            rename.insert({state, 1});
            groups[1].insert(state);
        }
        else{
            rename.insert({state, 0});
            groups[0].insert(state);
        }
    }
    bool createNew;
    bool notFound;
    int count = 2;
    std::queue<State> forDist;
    do{
        createNew = false;
        for(const auto& group: groups){
                State pattern = *group.second.begin();
            for(const auto& state: group.second){
                if(!compareState(a, rename, pattern, state)){
                    createNew = true;
                    forDist.push(state);
                }
            }
        }
        while(!forDist.empty()){
            notFound = true;
            int newCount = count;
            for(int i = newCount; i < count; i++){
                if(compareState(a, rename, *groups[i].begin(), forDist.front())){
                    groups[rename[forDist.front()]].extract(forDist.front());
                    groups[i].insert(forDist.front());
                    rename[forDist.front()] = i;
                    notFound = false;
                    break;
                }
            }
            if(notFound){
                groups[rename[forDist.front()]].extract(forDist.front());
                groups[count].insert({forDist.front()});
                rename[forDist.front()] = count++;
            }
            forDist.pop();
        }
    } while(createNew);
    a.m_States.clear();
    std::map<std::pair<State, Symbol>, State> newTransition;
    std::set<State> newFinal;
    for(int i = 0; i < count; i++){
        a.m_States.insert(rename[*groups[i].begin()]);
        if(a.m_FinalStates.contains(*groups[i].begin()))
            newFinal.insert(rename[*groups[i].begin()]);
        for(const auto& alfa: a.m_Alphabet){
            if(a.m_Transitions.contains({*groups[i].begin(), alfa}))
                newTransition.insert({{rename[*groups[i].begin()], alfa}, rename[a.m_Transitions.at({*groups[i].begin(), alfa})]});
        }
    }
    a.m_FinalStates = newFinal;
    a.m_Transitions.clear();
    a.m_Transitions = newTransition;
}

void print(DFA & a){
    std::cout << a.m_InitialState << std::endl;
    for(const auto& x: a.m_States)
        std::cout << x << " ";
    std::cout << std::endl;
    for(const auto& x: a.m_Alphabet)
        std::cout << x << " ";
    std::cout << std::endl;
    for(const auto& x: a.m_Transitions)
        std::cout << x.first.first << " " << x.first.second << "-" << x.second << std::endl;
    for(const auto& x: a.m_FinalStates)
        std::cout << x << " ";
    std::cout << std::endl;
}

void print(NFA & a){
    std::cout << a.m_InitialState << std::endl;
    for(const auto& x: a.m_States)
        std::cout << x << " ";
    std::cout << std::endl;
    for(const auto& x: a.m_Alphabet)
        std::cout << x << " ";
    std::cout << std::endl;
    for(const auto& x: a.m_Transitions)
        for(const auto& y: x.second)
            std::cout << x.first.first << " " << x.first.second << "-" << y << std::endl;
    for(const auto& x: a.m_FinalStates)
        std::cout << x << " ";
    std::cout << std::endl;
}

DFA unify(const NFA& a, const NFA& b){
    DFA result;
    NFA nfa1 = total(a);
    NFA nfa2 = total(b);
    NFA tmp = paralelRun(nfa1, nfa2, &finalUnify);
    print(tmp);
    result = determinization(tmp);
    print(result);
    trim(result);
    minimalize(result);
    print(result);
    return result;
}

DFA intersect(const NFA& a, const NFA& b) {
    DFA result;
    std::cout << "OK1";
    NFA nfa1 = total(a);
    NFA nfa2 = total(b);
    NFA tmp = paralelRun(nfa1, nfa2, &finalIntersect);
    std::cout << "OK";
    result = determinization(tmp);
    trim(result);
    minimalize(result);
    print(result);
    return result;
}

#ifndef __PROGTEST__

// You may need to update this function or the sample data if your state naming strategy differs.
bool operator==(const DFA& a, const DFA& b)
{
    return std::tie(a.m_States, a.m_Alphabet, a.m_Transitions, a.m_InitialState, a.m_FinalStates) == std::tie(b.m_States, b.m_Alphabet, b.m_Transitions, b.m_InitialState, b.m_FinalStates);
}

int main()
{
    NFA a1{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {0, 1}},
            {{0, 'b'}, {0}},
            {{1, 'a'}, {2}},
        },
        0,
        {2},
    };
    NFA a2{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'a'}, {2}},
            {{2, 'b'}, {2}},
        },
        0,
        {2},
    };
    DFA a{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'a'}, {2}},
            {{2, 'b'}, {3}},
            {{3, 'a'}, {4}},
            {{3, 'b'}, {3}},
            {{4, 'a'}, {2}},
            {{4, 'b'}, {3}},
        },
        0,
        {2},
    };
    intersect(a1, a2);

    NFA b1{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {2, 3}},
            {{2, 'b'}, {2}},
            {{3, 'a'}, {4}},
        },
        0,
        {1, 4},
    };
    NFA b2{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'b'}, {1}},
            {{1, 'a'}, {2}},
            {{2, 'b'}, {3}},
            {{3, 'a'}, {4}},
            {{4, 'a'}, {4}},
            {{4, 'b'}, {4}},
        },
        0,
        {4},
    };
    DFA b{
        {0, 1, 2, 3, 4, 5, 6, 7, 8},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {3}},
            {{2, 'b'}, {4}},
            {{3, 'a'}, {5}},
            {{3, 'b'}, {6}},
            {{4, 'a'}, {7}},
            {{4, 'b'}, {4}},
            {{5, 'a'}, {5}},
            {{5, 'b'}, {4}},
            {{6, 'a'}, {8}},
            {{6, 'b'}, {4}},
            {{7, 'a'}, {5}},
            {{7, 'b'}, {4}},
            {{8, 'a'}, {8}},
            {{8, 'b'}, {8}},
        },
        0,
        {1, 5, 8},
    };
   unify(b1, b2);

    NFA c1{
        {0, 1, 2, 3, 4},
        {'a', 'b'},
        {
            {{0, 'a'}, {1}},
            {{0, 'b'}, {2}},
            {{2, 'a'}, {2, 3}},
            {{2, 'b'}, {2}},
            {{3, 'a'}, {4}},
        },
        0,
        {1, 4},
    };
    NFA c2{
        {0, 1, 2},
        {'a', 'b'},
        {
            {{0, 'a'}, {0}},
            {{0, 'b'}, {0, 1}},
            {{1, 'b'}, {2}},
        },
        0,
        {2},
    };
    DFA c{
        {0},
        {'a', 'b'},
        {},
        0,
        {},
    };
    intersect(c1, c2);

    NFA d1{
        {0, 1, 2, 3},
        {'i', 'k', 'q'},
        {
            {{0, 'i'}, {2}},
            {{0, 'k'}, {1, 2, 3}},
            {{0, 'q'}, {0, 3}},
            {{1, 'i'}, {1}},
            {{1, 'k'}, {0}},
            {{1, 'q'}, {1, 2, 3}},
            {{2, 'i'}, {0, 2}},
            {{3, 'i'}, {3}},
            {{3, 'k'}, {1, 2}},
        },
        0,
        {2, 3},
    };
    NFA d2{
        {0, 1, 2, 3},
        {'i', 'k'},
        {
            {{0, 'i'}, {3}},
            {{0, 'k'}, {1, 2, 3}},
            {{1, 'k'}, {2}},
            {{2, 'i'}, {0, 1, 3}},
            {{2, 'k'}, {0, 1}},
        },
        0,
        {2, 3},
    };
    DFA d{
        {0, 1, 2, 3},
        {'i', 'k', 'q'},
        {
            {{0, 'i'}, {1}},
            {{0, 'k'}, {2}},
            {{2, 'i'}, {3}},
            {{2, 'k'}, {2}},
            {{3, 'i'}, {1}},
            {{3, 'k'}, {2}},
        },
        0,
        {1, 2, 3},
    };
    intersect(d1, d2);
}
#endif

