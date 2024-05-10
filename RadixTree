-------------------------- MODULE RadixTree --------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT Key, Value

VARIABLES root

ASSUME /\ Key \in Seq(Nat)
       /\ Value \in Nat

Node == [key : Seq(Nat), children : SUBSET Node, value : Value \union {NULL}]

RECURSIVE Insert(_,_,_)
Insert(node, key, value) ==
    IF key = <<>> THEN [node EXCEPT !.value = value]
    ELSE LET prefix == FindPrefix(node.key, key)
             remainingKey == SubSeq(key, Len(prefix)+1, Len(key))
         IN  IF prefix = node.key
             THEN LET child == CHOOSE c \in node.children : 
                                 /\ Len(c.key) > 0
                                 /\ c.key[1] = key[Len(prefix)+1]
                  IN  IF child \in node.children
                      THEN [node EXCEPT !.children = (node.children \ {child}) \union {Insert(child, remainingKey, value)}]
                      ELSE [node EXCEPT !.children = node.children \union 
                                         {[key |-> remainingKey, children |-> {}, value |-> value]}]
             ELSE LET newNode == [key |-> remainingKey, 
                                  children |-> {[key |-> SubSeq(node.key, Len(prefix)+1, Len(node.key)), 
                                                 children |-> node.children, 
                                                 value |-> node.value]},
                                  value |-> value]
                  IN  [key |-> prefix, children |-> {newNode}, value |-> NULL]

RECURSIVE FindPrefix(_,_)
FindPrefix(key1, key2) ==
    IF key1 = <<>> \/ key2 = <<>> \/ key1[1] # key2[1]
    THEN <<>>
    ELSE <<key1[1]>> \o FindPrefix(Tail(key1), Tail(key2))

RECURSIVE Get(_,_)
Get(node, key) ==
    IF key = <<>> THEN node.value
    ELSE LET prefix == FindPrefix(node.key, key)
         IN  IF prefix = node.key
             THEN LET child == CHOOSE c \in node.children : 
                                 /\ Len(c.key) > 0
                                 /\ c.key[1] = key[Len(prefix)+1]
                  IN  IF child \in node.children
                      THEN Get(child, SubSeq(key, Len(prefix)+1, Len(key)))
                      ELSE NULL
             ELSE NULL

Init == root = [key |-> <<>>, children |-> {}, value |-> NULL]

Next == \E key \in Key, value \in Value : 
            root' = Insert(root, key, value)

Spec == Init /\ [][Next]_root

=============================================================================
