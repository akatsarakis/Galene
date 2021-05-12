------------------------------- MODULE Galene -------------------------------
\* Galene: is a linearizable protocol used in ccKVS of Scale-out ccNUMA [Eurosys'18]

EXTENDS     Integers,
            FiniteSets

CONSTANTS   G_NODES,
            G_MAX_VERSION
            
VARIABLES   msgs,
            nodeTS,
            nodeState, 
            nodeRcvedAcks,
            nodeLastWriteTS
            
\* all Galene (+ environment) variables
gvars == << msgs, nodeTS, nodeState, nodeRcvedAcks, nodeLastWriteTS>>

-------------------------------------------------------------------------------------

\* A buffer maintaining all network messages. Messages are only appended to this variable (not 
\* removed once delivered) intentionally to check protocols tolerance in dublicates and reorderings 
send(m) == msgs' = msgs \union {m}

\* Check if all acknowledgments for a write have been received                                                  
receivedAllAcks(n) == (G_NODES \ {n}) \subseteq nodeRcvedAcks[n]
        
equalTS(v1,tb1,v2,tb2) ==  \* Timestamp equality
    /\ v1 = v2
    /\ tb1 = tb2

greaterTS(v1,tb1,v2,tb2) == \* Timestamp comparison
    \/ v1 > v2
    \/ /\   v1 = v2
       /\  tb1 > tb2

-------------------------------------------------------------------------------------

GMessage ==  \* Messages exchanged by the Protocol   
    [type: {"INV", "ACK"}, sender    : G_NODES,
                           version   : 0..G_MAX_VERSION,  
                           tieBreaker: G_NODES] 
        \union
    \* Note that we need not send Value w/ VALs, timestamp suffice to check consistency
    [type: {"VAL"},        version   : 0..G_MAX_VERSION, 
                           tieBreaker: G_NODES] 

GTypeOK ==  \* The type correctness invariant
    /\  msgs            \subseteq GMessage
    /\ \A n \in G_NODES: nodeRcvedAcks[n] \subseteq (G_NODES \ {n})
    /\  nodeLastWriteTS \in [G_NODES -> [version   : 0..G_MAX_VERSION,
                                       tieBreaker: G_NODES         ]]
    /\  nodeTS          \in [G_NODES -> [version   : 0..G_MAX_VERSION,
                                       tieBreaker: G_NODES         ]]
    /\  nodeState       \in [G_NODES -> {"valid", "invalid", "invalid_write", "write"}]
                                              

\* The consistent invariant: all alive nodes in valid state should have the same value / TS         
GConsistent == 
    \A k,s \in G_NODES   :  \/ nodeState[k] /= "valid"
                            \/ nodeState[s] /= "valid" 
                            \/ nodeTS[k] = nodeTS[s]
                                              
GInit == \* The initial predicate
    /\  msgs            = {}
    /\  nodeRcvedAcks   = [n \in G_NODES |-> {}]
    /\  nodeState       = [n \in G_NODES |-> "valid"]
    /\  nodeTS          = [n \in G_NODES |-> [version |-> 0, 
                                              tieBreaker |-> 
                                              CHOOSE k \in G_NODES: 
                                               \A m \in G_NODES: k <= m]]
    /\  nodeLastWriteTS = [n \in G_NODES |-> [version |-> 0, 
                                              tieBreaker |-> 
                                              CHOOSE k \in G_NODES: 
                                               \A m \in G_NODES: k <= m]]

-------------------------------------------------------------------------------------

g_upd_state(n, newVersion, newTieBreaker, newState, newAcks) == 
    /\  nodeRcvedAcks'    = [nodeRcvedAcks   EXCEPT ![n] = newAcks]
    /\  nodeState'        = [nodeState       EXCEPT ![n] = newState]
    /\  nodeTS'           = [nodeTS          EXCEPT ![n].version    = newVersion, 
                                                    ![n].tieBreaker = newTieBreaker]
    /\  nodeLastWriteTS'  = [nodeLastWriteTS EXCEPT ![n].version    = newVersion, 
                                                    ![n].tieBreaker = newTieBreaker]
                                            
g_send_inv_or_ack(n, newVersion, newTieBreaker, msgType) ==  
    /\  send([type        |-> msgType,
              sender      |-> n,
              version     |-> newVersion, 
              tieBreaker  |-> newTieBreaker])              

g_actions_for_upd(n, newVersion, newTieBreaker, newState, newAcks) == 
    /\  g_upd_state(n, newVersion, newTieBreaker, newState, newAcks)
    /\  g_send_inv_or_ack(n, newVersion, newTieBreaker, "INV")
 
-------------------------------------------------------------------------------------

GRead(n) ==  \* Execute a read
    /\ nodeState[n] = "valid"
    /\ UNCHANGED <<msgs, nodeTS, nodeState, nodeRcvedAcks, nodeLastWriteTS>>
              
GWrite(n) == \* Execute a write
    \* writes in invalid state are also supported as an optimization
    /\  nodeState[n]      \in {"valid"}
    /\  nodeTS[n].version < G_MAX_VERSION \* Only to configurably terminate the model checking 
    /\  g_actions_for_upd(n, nodeTS[n].version + 1, n, "write", {})


GRcvAck(n) ==   \* Process received Ack
    \E m \in msgs: 
        /\ m.type     = "ACK"
        /\ m.sender  /= n
        /\ m.sender  \notin nodeRcvedAcks[n]
        /\ equalTS(m.version, m.tieBreaker,
                   nodeLastWriteTS[n].version, 
                   nodeLastWriteTS[n].tieBreaker)
        /\ nodeState[n] \in {"write", "invalid_write"}
        /\ nodeRcvedAcks' = [nodeRcvedAcks EXCEPT ![n] = 
                                              nodeRcvedAcks[n] \union {m.sender}]
        /\ UNCHANGED <<msgs, nodeLastWriteTS, nodeTS, nodeState>>


GSendVals(n) == \* Send validations once acknowledments are received from all alive nodes
    /\ nodeState[n] \in {"write"}
    /\ receivedAllAcks(n)
    /\ nodeState'         = [nodeState EXCEPT![n] = "valid"]
    /\ send([type        |-> "VAL", 
             version     |-> nodeTS[n].version, 
             tieBreaker  |-> nodeTS[n].tieBreaker])
    /\ UNCHANGED <<nodeTS, nodeLastWriteTS, nodeRcvedAcks>>
 
GCoordinatorActions(n) ==   \* Coordinator actions for reads or writes
    \/ GRead(n)          
    \/ GWrite(n)         
    \/ GRcvAck(n)
    \/ GSendVals(n) 

-------------------------------------------------------------------------------------               
    
GRcvInv(n) ==  \* Process received invalidation
    \E m \in msgs: 
        /\ m.type     = "INV"
        /\ m.sender  /= n
        \* always acknowledge a received invalidation (irrelevant to the timestamp)
        /\ send([type       |-> "ACK",
                 sender     |-> n,   
                 version    |-> m.version,
                 tieBreaker |-> m.tieBreaker])
        /\ IF greaterTS(m.version, m.tieBreaker,
                        nodeTS[n].version, nodeTS[n].tieBreaker)
           THEN   /\ nodeTS' = [nodeTS EXCEPT ![n].version    = m.version,
                                          ![n].tieBreaker = m.tieBreaker]
                  /\ IF nodeState[n] \in {"valid", "invalid"}
                     THEN 
                        nodeState' = [nodeState EXCEPT ![n] = "invalid"]
                     ELSE 
                        nodeState' = [nodeState EXCEPT ![n] = "invalid_write"] 
           ELSE
                  UNCHANGED <<nodeState, nodeTS>>
        /\ UNCHANGED <<nodeLastWriteTS, nodeRcvedAcks>>
     
            
GRcvVal(n) ==   \* Process received validation
    \E m \in msgs: 
        /\ nodeState[n] /= "valid"
        /\ m.type = "VAL"
        /\ equalTS(m.version, m.tieBreaker,
                   nodeTS[n].version, 
                   nodeTS[n].tieBreaker)
        /\ nodeState' = [nodeState EXCEPT ![n] = "valid"]
        /\ UNCHANGED <<msgs, nodeTS, nodeLastWriteTS, nodeRcvedAcks>>
   
GFollowerActions(n) ==  \* Follower actions for writes 
    \/ GRcvInv(n)
    \/ GRcvVal(n) 
 
------------------------------------------------------------------------------------- 

GNext == \* Coordinator and Follower actions
    \E n \in G_NODES:       
            \/ GFollowerActions(n)
            \/ GCoordinatorActions(n)


G_Spec == GInit /\ [][GNext]_gvars


THEOREM G_Spec =>([]GTypeOK) /\ ([]GConsistent)

=============================================================================