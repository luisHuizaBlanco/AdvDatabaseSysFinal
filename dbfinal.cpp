/*

Document for Replicated Concurrency Control and Recovery Project 

by Luis Huiza Blanco

email: lgh7953@nyu.edu


*/


#include <iostream>
#include <vector>
#include <map>
#include <queue>
#include <regex>
#include <utility>
#include <array>
#include <queue>
#include <set>
#include <stack>
#include <string>
#include <climits>
#include <algorithm>

int TM_time = 1;

//

class Transaction
{
public:

    Transaction(int _id): trans_id(_id), start_time(TM_time) {}

    int getId() const 
    {
        return trans_id;
    }

    int getStartTime() const 
    {
        return start_time;
    }

    //gets a map with all the variables T cant read from X sites
    void setVariableCopiesTCannotRead(std::map<int, std::array<bool, 10>> cant_read)
    {
        variableCopiesTCannotRead = cant_read;
    }

    //need use this to check if a read should not happen on a site, because there wasnt a committed value between
    //the last time it recovered and the time T began
    bool T_CannotReadFromThisSite(int var_id, int site_id)
    {
        return variableCopiesTCannotRead[var_id][site_id - 1];
    }


private:

    int trans_id;
    int start_time;
    std::map<int, std::array<bool, 10>> variableCopiesTCannotRead;
};

//VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV

//to be used for checking for writes on sites that failed and to check for cycle failures
class TransactionRecord 
{

public:

    int transaction_id;
    int site_id;
    int var_id;
    int write_time;
    std::string type;

    TransactionRecord(int trans_id, int site, int var, int ctime, std::string op_type): 
    transaction_id(trans_id), site_id(site), var_id(var), write_time(ctime), type(op_type) {}
};

//VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV

//to store replicated variable Writes that need to be spread to all running sites
class ReplicatedVariableUpdate 
{

public:

    int site_id;
    int var_id;
    int write_time;

    ReplicatedVariableUpdate(int variable_id, int new_val, int ctime): var_id(variable_id), site_id(new_val), write_time(ctime) {}
};

//VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV

//variation of TransactionRecord made for the purpose of populating the DAG graph to detect cycles
class DAGNode 
{

public:
    int transaction_id;
    int var_id;
    int write_time;
    std::string type;

    DAGNode(int trans_id, int var, int ctime, std::string op_type)
        : transaction_id(trans_id), var_id(var), write_time(ctime), type(op_type) {}

    //comparison operator for use in std::map and std::set
    bool operator<(const DAGNode& other) const 
    {
        //we use as the unique identifier write time since no two entries will have the same write time
        return std::tie(write_time) < std::tie(other.write_time);
    }

};

//VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV

//directed acyclic graph for detecting cycles in the transactions
class DAG 
{

public:
    //adds an edge to the graph
    void addEdge(const DAGNode& from, const DAGNode& to) 
    {
        graph[from].insert(to);
        if (graph.find(to) == graph.end()) 
        {
            //makes sure theres a node [to] on the graph
            graph[to] = {}; 
        }
    }

    //adds a node to the graph
    void addNode(const DAGNode& from) 
    {
        graph[from] = {};
    }

    //remove a node and its edges
    void removeNode(const DAGNode& node) 
    {
        graph.erase(node);
        for (auto& [key, neighbors] : graph) 
        {
            neighbors.erase(node);
        }
    }

    //detect cycles in the graph
    bool detectCycle() 
    {
        std::map<DAGNode, bool> visited;
        std::map<DAGNode, bool> recursionStack;

        for (const auto& [node, _] : graph) 
        {
            if (!visited[node]) 
            {
                if (detectCycleUtil(node, visited, recursionStack)) 
                {
                    return true;
                }
            }
        }
        return false;
    }

    bool processTransactionNodes(const std::vector<DAGNode>& nodes, int trans_id) 
    {
        size_t nodes_size = nodes.size();

        std::vector<DAGNode> transactionNodes;

        //makes a vector with all the nodes from the transaction being added
        for (const auto& node : nodes) 
        {
            if (node.transaction_id == trans_id) 
            {
                transactionNodes.push_back(node);
                addNode(node);
            }
        }

        //we keep track of the edges made
        std::vector<std::pair<DAGNode, DAGNode>> addedEdges;

        //we add edges to every node from the earliest operation to the oldest
        for (size_t i = 0; i < nodes_size; ++i) 
        {
            int from = i;

            if(i < nodes_size - 1)
            {
                for (size_t j = i + 1; j < nodes_size; ++j) 
                {
                    int to = j;

                    if (from == to) continue;

                    if(nodes[from].transaction_id == nodes[to].transaction_id)
                    {
                        addEdge(nodes[from], nodes[to]);
                        addedEdges.emplace_back(nodes[from], nodes[to]);

                        break;
                    }
                }

            }
        }

        //Rule 2

        //[i] for current node, [j] give the next in reverse
        for (int i = nodes_size - 1; i >= 0; --i)
        {
            int from = i;

            for (int j = i - 1; j >= 0; --j)
            {
                int to = j;

                if (from == to) continue;

                if(nodes[from].type == "write")
                {
                    // if (graph[nodes[to]].find(nodes[from]) == graph[nodes[to]].end())
                    // {
                        if(nodes[to].var_id == nodes[from].var_id)
                        {
                            if(nodes[to].transaction_id != nodes[from].transaction_id)
                            {
                                addEdge(nodes[from], nodes[to]);
                                addedEdges.emplace_back(nodes[from], nodes[to]);

                                break;
                            }
                        }
                    // }
                }
                else if(nodes[to].type == "write")
                {
                    if(nodes[to].var_id == nodes[from].var_id)
                    {
                        if(nodes[to].transaction_id != nodes[from].transaction_id)
                        {
                            addEdge(nodes[to], nodes[from]);
                            addedEdges.emplace_back(nodes[to], nodes[from]);

                            break;
                        }                    
                    }
                }
            }
        }

        //we then check for cycles
        if (detectCycle()) 
        {
            
            // If a cycle is detected, remove all added nodes and edges
            for (const auto& node : transactionNodes) 
            {
                removeNode(node);
            }
            return false;
        }

        //no cycles, we clean the edges on the graph so they can be update
        for (const auto& [from, to] : addedEdges) 
        {
            removeEdge(from, to);
        }

        return true;
    }

private:
    std::map<DAGNode, std::set<DAGNode>> graph;

    // Helper for removing an edge
    void removeEdge(const DAGNode& from, const DAGNode& to) 
    {
        graph[from].erase(to);
    }

    // Helper function for DFS-based cycle detection
    bool detectCycleUtil(const DAGNode& node, std::map<DAGNode, bool>& visited, std::map<DAGNode, bool>& recursionStack) 
    {
        visited[node] = true;
        recursionStack[node] = true;

        for (const DAGNode& neighbor : graph[node]) 
        {
            if (!visited[neighbor] && detectCycleUtil(neighbor, visited, recursionStack)) 
            {
                return true;
            } 
            else if (recursionStack[neighbor]) 
            {
                return true;
            }
        }

        recursionStack[node] = false;
        return false;
    }
};

//VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV

//Data Manager for all intents and purposes
class Site
{
public:

    Site(int _s_id, bool site = false): site_id(_s_id), IsSiteDown(site)
    {
        //initializes all the variables in the site
        for(int i = 2; i < 21; i += 2)
        {
            variables_onsite[i] = {i * 10, TM_time};
        }

        if(_s_id % 2 == 0)
        {
            int i = _s_id - 1;

            variables_onsite[i] = {i * 10, TM_time};

            variables_onsite[i + 10] = {(i + 10) * 10, TM_time};
        }
    }

    int getId() const 
    {
        return site_id;
    }

    void siteFailure()
    {
        IsSiteDown = true;
    }

    void siteRecover()
    {
        IsSiteDown = false;
    }

    void addToChangesToBeCommitted(int trans_id, int var_id, int new_value)
    {
        //adds writes sent to this site to wait if their transaction commits or aborts
        int current_time = TM_time;

        changes_to_be_committed[{trans_id, current_time}] = {var_id, new_value};
    }

    void readMultiversionCopy(int trans_id, int var_id)
    {
        //allows transaction T to read the available copy of variables in the site made when T began
        auto outer_it = mvc_copies.find(trans_id);

        if (outer_it != mvc_copies.end()) 
        {
            auto inner_it = outer_it->second.find(var_id);

            if (inner_it != outer_it->second.end()) 
            {
                int value_from_copy = inner_it->second.first;

                bool unique_var = (var_id % 2 != 0);

                std::cout << "x" << var_id;
                if (!unique_var) 
                {
                    std::cout << "." << site_id;
                }
                std::cout << ": " << value_from_copy << std::endl;

            } 
        } 
    }

    bool areTransactionsOnSiteValid(const Transaction& T) 
    {
        //we get the id and start time of a transaction T
        int transaction_id = T.getId();
        int start_time = T.getStartTime();

        for (const auto& entry : changes_to_be_committed) 
        {
            int entry_trans_id = entry.first.first;
            int entry_write_time = entry.first.second;
            int entry_var_id = entry.second.first;
            int entry_new_value = entry.second.second;

            //we look through changes to be committed for any Writes made by T
            if (entry_trans_id == transaction_id) 
            {
                // Check if the variable's last committed time
                auto it = variables_onsite.find(entry_var_id);

                if (it != variables_onsite.end()) 
                {
                    int last_committed_time = it->second.second;

                    //if the last commit is more recent than the W made, another T committed first (first commit wins, others abort)
                    if (last_committed_time > start_time) 
                    {
                        return false;
                    }
                }
            }
        }

        return true;
    }

    void makeReadCopyOfVariables(const Transaction& T)
    {
        //we make a copy of available variables for reads to this site
        int transaction_id = T.getId();

        mvc_copies[transaction_id] = variables_onsite;
    }

    std::vector<ReplicatedVariableUpdate> commitWritesFromT(const Transaction& T)
    {
        int transaction_id = T.getId();

        std::vector<ReplicatedVariableUpdate> data_to_replicate;

        //look for entries in changes to be committed
        for (auto it = changes_to_be_committed.begin(); it != changes_to_be_committed.end();) 
        {
            int entry_trans_id = it->first.first;
            int entry_write_time = it->first.second;
            int entry_var_id = it->second.first;
            int entry_new_value = it->second.second;

            //check if an entry is from a transaction
            if (entry_trans_id == transaction_id) 
            {
                //commit new values to the site
                if (variables_onsite.find(entry_var_id) != variables_onsite.end()) 
                {
                    variables_onsite[entry_var_id] = {entry_new_value, TM_time};
                }

                if(entry_var_id % 2 == 0)
                {
                    data_to_replicate.push_back(ReplicatedVariableUpdate(entry_var_id, entry_new_value, entry_write_time));
                }

                //erase the entry from changes_to_be_committed
                it = changes_to_be_committed.erase(it);
            } 
            else 
            {
                ++it;
            }
        }

        return data_to_replicate;
    }

    void abortWritesFromTransaction(const Transaction& T)
    {
        int transaction_id = T.getId();

        for (auto it = changes_to_be_committed.begin(); it != changes_to_be_committed.end();) 
        {
            int entry_trans_id = it->first.first;
            int entry_var_id = it->second.first;
            int entry_new_value = it->second.second;

            //check if an entry is from transaction T that is being aborted
            if (entry_trans_id == transaction_id) 
            {
                //erase the entry from changes_to_be_committed
                it = changes_to_be_committed.erase(it);
            }
            else
            {
                ++it;
            }
        }
    }

    void UpdateReplicatedVariables(int var_id, int new_value)
    {
        //used only when a replicated variable is written to on another site to update the copy on this
        variables_onsite[var_id] = {new_value, TM_time};
    }

    bool getIsSiteDown() const
    {
        return IsSiteDown;
    }

    void siteState()
    {
        std::cout << "site " << site_id << " " << std::endl;

        for (auto& var : variables_onsite)
        {
            std::cout << " x" << var.first << ": " << var.second.first;
        }

        std::cout << std::endl;
    }

    std::map<int, std::pair<int, int>> getVariablesOnSite() const
    {
        return variables_onsite;
    }

private:

    int site_id;
    bool IsSiteDown;

    //read copies
    //transaction id, <variable id, <last committed value, last committed time>>
    std::map<int, std::map<int, std::pair<int, int>>> mvc_copies;

    //committed values on the site
    //variable id, <last committed value, last committed time>
    std::map<int, std::pair<int, int>> variables_onsite;

    //writes on the site waiting to see if their transaction is committed or aborted
    //<transaction id, time of write> <variable id, new value>
    std::map<std::pair<int, int>, std::pair<int, int>> changes_to_be_committed;

};

//VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV

class TransactionManager 
{
public:

    void beginTransaction(int _id)
    {
        //we create a transaction object T
        Transaction T(_id);

        //we give it a list of variables that he cant read in the specified sites
        T.setVariableCopiesTCannotRead(variableCopiesToNotRead); 

        //T is added to the transactions vector
        transactions.push_back(T);

        //The sites prepare a copy of all their variables for T to read
        for (auto& site : sites)
        {
            site.makeReadCopyOfVariables(T);
        }

        std::cout << "T" << _id << " begins" << std::endl;
    }

    void endTransaction(int trans_id)
    {
        //we look for the transaction we are ending on transactions
        for (auto it = transactions.begin(); it != transactions.end(); ++it) 
        {
            if (it->getId() == trans_id) 
            {   
                Transaction& T = *it;

                bool isValid = true;

                // std::cout << "checking for writes in downed sites \n";

                //we check to make sure the transaction didnt do Writes on a site that later failed
                isValid = CheckForWriteOnAFailedSite(T);

                //we check that all writes the transaction made fulfill the condition "first committer wins"
                if (isValid)
                {
                    // std::cout << "checking if all transactions are valid \n";

                    for (auto& site : sites)
                    {
                        //probably rename function to checkFirstCommitterWins
                        if (!site.areTransactionsOnSiteValid(T)) 
                        {
                            isValid = false;
                        }
                    }
                }

                //work in progress
                if (isValid)
                {
                    // std::cout << "checking for cycles \n";
                    isValid = checkForRWandWWCycles(T);
                } 

                //std::cout << "deciding if to commit or abort \n";
                if (isValid) 
                {
                    transactionCommit(T);
                }
                else 
                {
                    transactionAbort(T);
                }

                //remove transaction from the transactions vector
                transactions.erase(it);

                //std::cout << "Transactions size: " << transactions.size() << std::endl;

                return;
            }
        }
    }

    void transactionCommit(Transaction T)
    {
        std::cout << "T" << T.getId() << " commits" << std::endl;

        //vector to keep track replicated variables were committing new values to
        std::vector<ReplicatedVariableUpdate> data_to_replicate;

        for (auto& site : sites)
        {
            //we commit all writes to each site, and get back a vector with all the replicated variables written to and their new values
            std::vector<ReplicatedVariableUpdate> update = site.commitWritesFromT(T);

            //if update had any replicated variables to update
            if(!update.empty())
            {
                //we insert those to data_to_replicate
                data_to_replicate.insert(data_to_replicate.end(), update.begin(), update.end());
            }
        }

        //if a replicated variable was written on
        if(!data_to_replicate.empty())
        {
            //we loop through data to replicate and propagate the new values to the other sites
            for(const auto& data : data_to_replicate)
            {
                int var_id = data.var_id;
                int new_value = data.site_id;
                int write_time = data.write_time;

                PropagateValueToRunningSites(var_id, new_value, write_time);
            }
        }
    }

    void transactionAbort(Transaction T)
    {
        std::cout << "T" << T.getId() << " aborts" << std::endl;

        //we remove all entries of attempted Writes from the aborted transaction in all sites
        for (auto& site : sites)
        {
            site.abortWritesFromTransaction(T);
        }

        //std::cout << "end aborting \n";
    }

    void startReadRequest(int trans_id, int var_id)
    {
        //read request function

        //if the read is for an even indexed variable
        if (var_id % 2 == 0)
        {
            //Use the variableCopiesTCannotRead from T to determine from which sites it can or cannot Read
            //If no site has a committed value T can read, abort T
            //If there a site with a committed value but it is down, T must be put on queue to wait to do the Read

            for (auto it = transactions.begin(); it != transactions.end(); ++it) 
            {
                if (it->getId() == trans_id) 
                {   
                    Transaction& T = *it;

                    //
                    //int singleSiteWithWrite;

                    for (auto& site : sites)
                    {
                        int site_id = site.getId();

                        //we check if the value is readable in this site, if not, we skip
                        if(T.T_CannotReadFromThisSite(var_id, site_id)) continue;

                        if(site.getIsSiteDown())
                        {
                            //add to Read queue for the site
                            std::cout << "read queued until site " << site_id << " recovers "<< std::endl;

                            queuedReads[site_id].push({trans_id, var_id});
                        }
                        else
                        {
                            site.readMultiversionCopy(trans_id, var_id);

                            //add to transaction_records
                            transaction_records.push_back(TransactionRecord(trans_id, site.getId(), var_id, TM_time, "read"));
                        }

                        return;
                    }

                    //if there are no readable sites, abort T
                    transactionAbort(T);

                    transactions.erase(it);

                    return;
                }
            }

        }
        else//if the read is for an odd indexed variable
        {
            //we look for the site that has it
            int site_id = var_id + 1;

            if(site_id > 9) site_id -= 10;

            for (auto& site : sites)
            {
                if(site.getId() == site_id)
                {
                    //if its running, we read the copy of the variables from when T began
                    if(site.getIsSiteDown()) continue;

                    site.readMultiversionCopy(trans_id, var_id);

                    //add to transaction_records
                    transaction_records.push_back(TransactionRecord(trans_id, site.getId(), var_id, TM_time, "read"));

                    break;
                }
            }
        }
    }

    void startWriteRequest(int trans_id, int var_id, int new_value)
    {
        //we check if the variable is replicated or not
        if (var_id % 2 == 0)
        {
            //if its replicated, we check through all sites to look for one we can do the write in
            for (auto& site : sites)
            {
                //if the site isnt down we send the Write
                if(site.getIsSiteDown()) continue;

                site.addToChangesToBeCommitted(trans_id, var_id, new_value);

                //and add the operation to the transaction records
                transaction_records.push_back(TransactionRecord(trans_id, site.getId(), var_id, TM_time, "write"));

                break;
            }
        }
        else
        {
            //if its a unique variable, we look for the site it is located in and send the write to it
            int site_id = var_id + 1;

            if(site_id > 9) site_id -= 10;

            for (auto& site : sites)
            {
                //if the site isnt down we send the Write
                if(site.getIsSiteDown()) continue;

                if(site.getId() == site_id)
                {
                    site.addToChangesToBeCommitted(trans_id, var_id, new_value);

                    //and add the operation to the transaction records
                    transaction_records.push_back(TransactionRecord(trans_id, site.getId(), var_id, TM_time, "write"));

                    break;
                }
            }
        }
    }

    void PropagateValueToRunningSites(int var_id, int new_value, int write_time)
    {
        for (auto& site : sites)
        {
            int site_id = site.getId();
            int last_failure_time = site_failure_history[site.getId()].first;
            int last_recovery_time = site_failure_history[site.getId()].second;
            bool isSiteDownDuringWrite = (last_failure_time > last_recovery_time);

            if (last_failure_time > write_time) continue;

            ////

            //if a site is down on commit or was down during the write, it should not get the updated value
            if (site.getIsSiteDown() || write_time < last_recovery_time)
            {
                //mark this variable to not be read if the write happened while it was down
                variableCopiesToNotRead[var_id][site_id - 1] = true;
                continue;
            }

            site.UpdateReplicatedVariables(var_id, new_value);

            // if the copy of a variable in this site was marked to not be read, 
            // now that it has an up to date write, we can unmark it so it can be read from
            variableCopiesToNotRead[var_id][site_id - 1] = false;

        }
    }

    bool CheckForWriteOnAFailedSite(Transaction T)
    {
        //we check that the transaction did not make a Write on a site that later failed
        int trans_id = T.getId();

        //we check the transaction records
        for (auto& record : transaction_records)
        {
            //for any entry with the id of the transaction were checking
            if (record.transaction_id == trans_id)
            {
                int site_id = record.site_id;
                int var_id = record.var_id;
                int write_time = record.write_time;

                //if the write was on a replicated variable, all sites are checked
                if(var_id % 2 == 0)
                {
                    for (const auto& site_history : site_failure_history)
                    {
                        int last_failure_time = site_history.second.first;

                        //if the write time is less than the last failure time, the failure happened after the write, so we return false
                        if (write_time < last_failure_time)
                        {
                            return false;
                        }
                    }
                }
                else //if its unique, we only check the site the variable is in
                {
                    auto it = site_failure_history.find(site_id);

                    if (it != site_failure_history.end())
                    {
                        int last_failure_time = site_failure_history[site_id].first;

                        //if the write time is less than the last failure time, the failure happened after the write, so we return false
                        if (write_time < last_failure_time)
                        {
                            return false;
                        }
                    }
                }
            }
        }

        return true;
    }

    void makeSiteFail(int site_id)
    {
        //we loop through the sites
        for (auto& site : sites)
        {
            //when we find the site, it is set to be down, and we update its failure history
            if (site.getId() == site_id) 
            {
                site.siteFailure();
                std::cout << "site " << site_id << " fails." << std::endl;
                site_failure_history[site.getId()].first = TM_time;

                //we also mark its copy of all replicated variable as not readable until a write is made to it
                for(int i = 2; i < 21; i += 2)
                {
                    variableCopiesToNotRead[i][site_id - 1] = true;
                }

                return;
            }
        }
    }

    void makeSiteRecover(int site_id)
    {
        //we loop through the sites
        for (auto& site : sites)
        {
            //when we find the site, it is set to be recovered, and we update its failure history
            if (site.getId() == site_id) 
            {
                site.siteRecover();
                std::cout << "site " << site_id << " recovers." << std::endl;
                site_failure_history[site.getId()].second = TM_time;

                auto it = queuedReads.find(site_id);

                //check if the site had any queued reads
                if (it != queuedReads.end())
                {

                    //if the queuedReads queue isnt empty
                    if (!queuedReads[site_id].empty())
                    {
                        std::cout << "site " << site_id << " has queued reads" << std::endl;

                        //we copy the queue
                        std::queue<std::pair<int, int>> readsToDo = queuedReads[site_id];

                        //clear the queue in the queuedReads entry
                        while (!queuedReads[site_id].empty())
                        {
                            queuedReads[site_id].pop();
                        }

                        //execute the pending reads to the site
                        while (!readsToDo.empty())
                        {
                            auto pair = readsToDo.front();
                            
                            int trans_id = pair.first;
                            int var_id = pair.second;

                            site.readMultiversionCopy(trans_id, var_id);

                            //add to transaction_records
                            transaction_records.push_back(TransactionRecord(trans_id, site.getId(), var_id, TM_time, "read"));

                            readsToDo.pop();
                        }
                    }
                }

                return;
            }
        }
    }

    void dump()
    {
        //prints all the changes done to variables
        std::map<int, int> evenVariablePrinted;

        for (auto& site : sites)
        {
            auto variables = site.getVariablesOnSite();

            for (auto& var : variables)
            {
                int var_id = var.first;
                int var_value = var.second.first;
                int initial_value = var_id * 10;

                if (var_value != initial_value)
                {
                    if (var_id % 2 == 0) //even indexed variable
                    {
                        if (evenVariablePrinted.find(var_id) == evenVariablePrinted.end())
                        {
                            std::cout << "x" << var_id << ": " << var_value << " at all sites" << std::endl;
                            evenVariablePrinted[var_id] = var_value; // mark as printed
                        }
                    }
                    else //odd variable
                    {
                        std::cout << "x" << var_id << ": " << var_value << " at site " << site.getId() << std::endl;
                    }
                }
            }
        }

        std::cout << "All other variables have their initial values." << std::endl;
    }

    void queryState()
    {
        //for debugging use, lets me see the values in all sites
        for (auto& site : sites)
        {
            site.siteState();
        }
    }

    void InitializeProject()
    {
        //we create the 10 sites, and populate their failure history with 0s (means no failures or recoveries)
        for(int i = 1; i < 11; i++)
        {
            sites.push_back(Site(i));

            site_failure_history[i] = {0,0};
        }
    }

    std::vector<DAGNode> ConvertRecordToNode (int trans_id)
    {
        std::vector<DAGNode> dagNodes;

        for (const auto& record : transaction_records) 
        {
            if (record.transaction_id == trans_id) 
            {
                //convert TransactionRecord to DAGNode
                DAGNode node(record.transaction_id, record.var_id, record.write_time, record.type);
                dagNodes.push_back(node);
            }
        }

        return dagNodes;
    }

    void sortByWriteTime(std::vector<DAGNode>& nodes) 
    {
        std::sort(nodes.begin(), nodes.end(), [](const DAGNode& a, const DAGNode& b) {
            return a.write_time < b.write_time;
        });
    }

    bool isThereACycle(std::vector<DAGNode>& nodes, int trans_id)
    {
        sortByWriteTime(nodes);

        if (dag.processTransactionNodes(nodes, trans_id)) 
        {
            return false;
        } 
        else 
        {
            //there is not cycle made with these nodes
            return true;
        }
    }

    void removeNodesByTransactionId (int trans_id)
    {
        nodes.erase(
            std::remove_if(nodes.begin(), nodes.end(), [trans_id](const DAGNode& node) {
                return node.transaction_id == trans_id;
            }),
            nodes.end()
        );
    }

    bool checkForRWandWWCycles(Transaction T) 
    {
        //get all the TransactionRecords with the same transaction id as T
        //convert the TransactionRecords into DAGNodes
        //test the DAG with the new nodes
        //return false if it creates a cycle, return true if no cycles are formed

        int trans_id = T.getId();

        std::vector<DAGNode> update = ConvertRecordToNode(trans_id);

        if(!update.empty())
        {
            //we insert those to data_to_replicate
            nodes.insert(nodes.end(), update.begin(), update.end());
        }

        if(isThereACycle(nodes, trans_id))
        {
            removeNodesByTransactionId(trans_id);
            
            return false;
        }

        return true;
    }
    
private:

    std::vector<Transaction> transactions;
    std::vector<Site> sites;

    //site_id, <last failure, last recovery>
    std::map<int,std::pair<int, int>> site_failure_history;

    //keep track of transactions made to ensure to abort T if it writes to a site that then fails
    std::vector<TransactionRecord> transaction_records;

    //keeps track of what copies of variables to not read
    //<variable id, <array of booleans for each site>>
    //if bool = true, that copy must not be read
    std::map<int, std::array<bool, 10>> variableCopiesToNotRead;

    //reads that are waiting for a site to recover
    //site id, queue of <transaction id, var id> 
    std::map<int,std::queue<std::pair<int, int>>> queuedReads;

    //directed acyclic graph used to catch cycle errors
    DAG dag;
    
    std::vector<DAGNode> nodes;
};


//regex for all command line inputs
std::regex beginRegex("begin\\(T([1-9])\\)");
std::regex endRegex("end\\(T([1-9])\\)");
std::regex readRegex("R\\(T([1-9]),x(1[0-9]|20|[1-9])\\)");
std::regex writeRegex("W\\(T([1-9]),x(1[0-9]|20|[1-9]),(\\d{1,3})\\)");
std::regex failRegex("fail\\((10|[0-9])\\)");
std::regex recoverRegex("recover\\((10|[0-9])\\)");

void printTime()
{
    //std::cout << TM_time << std::endl;
}

int main(int argc, char** argv)
{
    std::string input;

    std::smatch match;

    std::cout << "Starting Concurrency Control Project"<< std::endl;

    TransactionManager TM;

    printTime();

    TM.InitializeProject();

    while (std::cin >> input)
    {
        if (std::regex_match(input, match, beginRegex)) 
        {
            TM.beginTransaction(stoi(match[1]));
            TM_time++;
            printTime();
        }

        if (std::regex_match(input, match, endRegex)) 
        {
            TM.endTransaction(stoi(match[1]));
            TM_time++;
            printTime();
        }

        if (std::regex_match(input, match, readRegex)) 
        {
            TM.startReadRequest(stoi(match[1]), stoi(match[2]));
            TM_time++;
            printTime();
        }

        if (std::regex_match(input, match, writeRegex)) 
        {
            TM.startWriteRequest(stoi(match[1]), stoi(match[2]), stoi(match[3]));
            TM_time++;
            printTime();
        }

        if (std::regex_match(input, match, failRegex)) 
        {
            TM.makeSiteFail(stoi(match[1]));
            TM_time++;
            printTime();
        }

        if (std::regex_match(input, match, recoverRegex)) 
        {
            TM.makeSiteRecover(stoi(match[1]));
            TM_time++;
            printTime();
        }

        if(input == "dump()")
        {
            TM.dump();
            TM_time++;
            printTime();
        }

        if(input == "querystate")
        {
            TM.queryState();
        }

        if(input == "exit")
        {
            break;
        }
    }  
}