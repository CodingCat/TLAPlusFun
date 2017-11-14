------------------------------- MODULE first -------------------------------

EXTENDS Integers
VARIABLES i, pc

Init == (pc = "start") /\ (i = 0)

Pick == \/ /\ pc = "start"
           /\ i' \in 0..1000
           /\ pc' = "middle"
           
Add1 ==  \/ /\ pc = "middle"
            /\ i' = i + 1
            /\ pc' = "done"
           
Next == Pick \/ Add1

=============================================================================
\* Modification History
\* Last modified Sun Nov 12 08:27:52 PST 2017 by nanzhu
\* Created Sat Nov 11 19:47:12 PST 2017 by nanzhu
