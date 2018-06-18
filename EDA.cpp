/*
 * Equivalence Checker for netlists
 *
 *
 * Name 1: Muhammad Arshan
 * Matriculation Number 1: 456678
 * 
 * Name 2: Muhammad Shiraz Alam Khan
 * Matriculation Number 2: 454939
 *
 */

#include <stdio.h>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <map>
#include <string>
#include <cstdlib>

using namespace std;

typedef enum
{
	AND,
	OR,
	INV,
	XOR
} GateType;

typedef struct
{
	GateType type;
	vector<int> nets;
} Gate;

typedef vector<Gate> GateList;

 // The following global variables are provided and automatically pre-filled (examples are for file xor2.net):

// Total number of nets in netlist 1 / 2
// E.g. netCount1 is 3
int netCount1, netCount2;

// Names of inputs / outputs in netlist 1 / 2
// E.g. inputs1[0] contains "a_0"
vector<string> inputs1, outputs1, inputs2, outputs2;

// Mapping from input / output names to net numbers in netlist 1 / 2
// E.g. map1["a_0"] is 1, map1["b_0"] is 2, ...
map<string, int> map1, map2;

// List (std::vector<Gate>) of all gates in netlist 1 / 2
// E.g.:
// - gates1[0].type is XOR
// - gates1[0].nets is std::vector<int> and contains three ints (one for each XOR port)
// - gates1[0].nets[0] is 1 (first XOR input port)
// - gates1[0].nets[1] is 2 (second XOR input port)
// - gates1[0].nets[2] is 3 (XOR output port)
GateList gates1, gates2;


int readFile(string filename, int & netCount, vector<string> & inputs, vector<string> & outputs, map<string, int> & map, GateList & gates)
{
	ifstream file(filename.c_str());
	if (! file.is_open())
	{
		return -1;
	}
	string curLine;
	// net count
	getline(file, curLine);
	netCount = atoi(curLine.c_str());
	// inputs
	getline(file, curLine);
	stringstream inputsStream(curLine);
	string buf;
	while (inputsStream >> buf)
	{
		inputs.push_back(buf);
	}
	// outputs
	getline(file, curLine);
	stringstream outputsStream(curLine);
	while (outputsStream >> buf)
	{
		outputs.push_back(buf);
	}
	// mapping
	for (size_t i=0; i<inputs1.size() + outputs1.size(); i++)
	{
		getline(file, curLine);
		stringstream mappingStream(curLine);
		mappingStream >> buf;
		int curNet = atoi(buf.c_str());
		mappingStream >> buf;
		map[buf] = curNet;
	}
	// empty line
	getline(file, curLine);
	if (curLine.length() > 1)
	{
		return -1;
	}
	// gates
	while (getline(file, curLine))
	{
		stringstream gateStream(curLine);
		gateStream >> buf;
		Gate curGate;
		if (buf != "and" && buf != "or" && buf != "inv" && buf != "xor")
		{
			cerr << "Unknown gate type: " << buf << endl;
			return -1;
		}
		curGate.type = (buf == "and" ? AND : buf == "or" ? OR : buf == "inv" ? INV : XOR);
		while (gateStream >> buf)
		{
			int curNet = atoi(buf.c_str());
			curGate.nets.push_back(curNet);
		}
		gates.push_back(curGate);
	}
	return 0;
}

int readFiles(string filename1, string filename2)
{
	if (readFile(filename1, netCount1, inputs1, outputs1, map1, gates1) != 0)
	{
		return -1;
	}
	if (readFile(filename2, netCount2, inputs2, outputs2, map2, gates2) != 0)
	{
		return -1;
	}
	return 0;
}

// use this method to print a CNF
void printCNF(vector< vector<int> > & cnf)
{
	for (size_t clauseNum = 0; clauseNum < cnf.size(); clauseNum++)
	{
		cout << (clauseNum==0 ? "" : " ") << "[";
		for (size_t litNum = 0; litNum < cnf[clauseNum].size(); litNum++)
		{
			cout << (litNum==0 ? "" : " ") << cnf[clauseNum][litNum];
		}
		cout << "]";
	}
	cout << endl;
}


//
// Add auxiliary functions here (if necessary)
//
void counter(vector<int> value)
{
	cout << "\nInputs: " << "\n" << "Equivalent input for both netlists \n";
	for(size_t i = 0; i < inputs1.size(); i++)
	{
		cout << inputs1[i] << ":" << value[map1[inputs1[i]]] << "\n";
	}
	cout << "\nOutputs: " << "\n" << "Netlist 1 \n";
	for(size_t i = 0; i < outputs1.size(); i++)
	{
		cout << outputs1[i] << ":" << value[map1[outputs1[i]]] << "\n";
	}
	cout << "\nOutputs: " << "\n" << "Netlist 2 \n";
	for(size_t i = 0; i < outputs2.size(); i++)
	{
		cout << outputs2[i] << ":" << value[netCount1 + map2[outputs2[i]]] << "\n";
	}
	exit(0);
}


void DP(vector< vector<int> > cnf, vector<int> value)
{
	//Unit Clause Rule
	int unitc;
	UnitClauseloop:
	unitc = 0;
	//for loop to check that is there any Unit clause in CNF.
	for(size_t u_clause = 0; u_clause < cnf.size(); u_clause++)
	{
		//Give the condition that if the size of cnf clause is 1
		if(cnf[u_clause].size() == 1)
		{
			//then we can shift that clause to position 0
			unitc = cnf[u_clause][0];
			//Now we can '.erase' which is a property of 'vector' so we can erase that particular clause
			//We can also use '.begin' which is a property of 'vector', it can define that where you want to start
			cnf.erase(cnf.begin() + u_clause);
		}
	}

	cout << "\nThe Unit Clause is: " << unitc << "\n";

	//for loop to check that, is there any clause in CNF.
	for(size_t u_clause = 0; u_clause < cnf.size(); u_clause++)
	{
		//For loop to check that how many clause number in the cnf with other literal
		for(size_t litCheck = 0; litCheck <	cnf[u_clause].size(); litCheck++)
		{
			//Give the condition that if cnf have that particular clause number with other literals
			if(cnf[u_clause][litCheck] == unitc)
			{
				//So we can erase that particular clause
				cnf.erase(cnf.begin() + u_clause) ;
			}
		}
	}

	//for loop to check that, is there any clause in CNF..
	for(size_t u_clause = 0; u_clause < cnf.size(); u_clause++)
	{
		//For loop to check that how many clause number in the cnf with other literal
		for(size_t litCheck = 0; litCheck <	cnf[u_clause].size(); litCheck++)
		{
			//Give the condition that if cnf have that particular clause number but with '-' sign with other literals
			if(cnf[u_clause][litCheck] == -unitc)
			{
				//So we can erase that particular clause number with '-' sign
				cnf[u_clause].erase(cnf[u_clause].begin() + litCheck);
			}
		}
	}

	cout << "Unit Clause \n";

	//for loop to check total number to clauses after erasing
	for(size_t clause = 0; clause < cnf.size(); clause++)
	{
		cout << "(";
		//For loop to check that how many literals in one clause
		for(size_t lit = 0; lit < cnf[clause].size(); lit++)
		{
			cout << cnf[clause][lit] << " ";
		}
		cout << ")";
	}

	if(unitc < 0)
	{
		value.at(abs(unitc)) = 0;
	}
	else
	{
		value.at(abs(unitc)) = 1;
	}

	for(size_t u_clause = 0; u_clause < cnf.size(); u_clause++)
	{
		//Give the condition that if the size of cnf clause is 1
		if(cnf[u_clause].size() == 1)
		{
			goto UnitClauseloop;
		}
	}

	// Add code for Davis Putnam algorithm here

	if(cnf.size() == 0)
	{
		cout << "Solution" << "Found!";
		cout << "\nCircuits are not Equivalent(Counter Example) :";
		counter(value);
		exit(0);
	}
	else
	{
		for(size_t i = 0; i < cnf.size(); i++)
		{
			if(cnf[i].size() == 0)
			{
				cout << "\n Circuits are Equal!";
				return;
			}
		}
	}

	// declare an integer
	int last_lit;
	//If CNF is not empty
	if(!cnf.empty())
	{
		//declare an vector<int> to get the size of the CNF
		vector<int> l = cnf[cnf.size() - 1];
		//an integer can store tha last value of the cnf and than make that value absolute
		last_lit = abs(l[l.size() - 1]);
		cout << endl << "\nLast Literal is: " << last_lit;
	}

	vector< vector<int> > cnf0, cnf1;
	vector<int> clause_value;
	int assign = 0;
	//For loop to check the size of CNF
	for(size_t num_clause = 0; num_clause < cnf.size(); num_clause++)
	{
		clause_value.clear();
		assign = 1;
		//For loop to check the size of CNF with literals
		for(size_t num_lit = 0; num_lit < cnf[num_clause].size(); num_lit++)
		{
			//if Cnf is equal to the last value of literal
			if(cnf[num_clause][num_lit] == last_lit)
			{
				//assign = 1;
			}
			//if Cnf is equal to the last value of literal but with '-'sign
			else if(cnf[num_clause][num_lit] == -last_lit)
			{
				assign = 0;
			}
			//if Cnf is not equal to the last value of literal but with '-'sign
			else if(cnf[num_clause][num_lit] != -last_lit)
			{
				//the CNF will be store in 'clause'
				clause_value.push_back(cnf[num_clause][num_lit]);
			}
		}
		if(assign == 1)
		{
			cnf0.push_back(clause_value);
		}
		//Declaring the value of last literal is '0'
		value.at(last_lit) = 0;
		cout << value[last_lit] << " ";
		cout << "cnf0 = ";
		//for loop to check total number to clauses
		for(size_t clause = 0; clause < cnf0.size(); clause++)
		{
			cout << "(";
			//For loop to check that how many literals in one clause
			for(size_t lit = 0; lit < cnf0[clause].size(); lit++)
			{
				cout << cnf0[clause][lit] << " ";
			}
			cout << ")";
		}
		DP(cnf0,value);
		for(size_t num_clause = 0; num_clause < cnf.size(); num_clause++)
		{
			clause_value.clear();
			assign = 1;
			//For loop to check the size of CNF with literals
			for(size_t num_lit = 0; num_lit < cnf[num_clause].size(); num_lit++)
			{
				//if Cnf is equal to the last value of literal but with '-'sign
				if(cnf[num_clause][num_lit] == -last_lit)
				{
					//assign = 1;
				}
				//if Cnf is equal to the last value of literal
				else if(cnf[num_clause][num_lit] == last_lit)
				{
					assign = 0;
				}
				//if Cnf is not equal to the last value of literal
				else if(cnf[num_clause][num_lit] != last_lit)
				{
					//the CNF will be store in 'clause'
					clause_value.push_back(cnf[num_clause][num_lit]);
				}
			}
			if(assign == 1)
			{
				cnf1.push_back(clause_value);
			}
		}

		cout << endl << "\nLast Literal is: " << last_lit;
		//Declaring the value of last literal is '0'
		value.at(last_lit) = 1;
		cout << value[last_lit] << " ";
		cout << "cnf1 = ";

		//for loop to check total number to clauses
		for(size_t clause = 0; clause < cnf1.size(); clause++)
		{
			cout << "(";
			//For loop to check that how many literals in one clause
			for(size_t lit = 0; lit < cnf1[clause].size(); lit++)
			{
				cout << cnf1[clause][lit] << " ";
			}
			cout << ")";
		}
		DP(cnf1,value);
	}
}

int main(int argc, char ** argv)
{
	if (argc != 3)
	{
		cerr << "Wrong argument count!\n";
		return -1;
	}
	if (readFiles(argv[1], argv[2]) != 0)
	{
		cerr << "Error while reading files!\n";
		return -1;
	}

	/*
	 * The following global variables are now defined (see above for data types and details):
	 * - netCount1, netCount2
	 * - inputs1, outputs1, inputs2, outputs2
	 * - map1, map2
	 * - gates1, gates2
	 */
	
	
	//
	// Add your code to build the CNF.
	// The CNF should be a vector of vectors of ints. Each "inner" vector represents one clause. The "outer" vector represents the whole CNF.
	//
	vector< vector<int> > cnf;
	//Input Pins Equivalent Function fc(a,b) = (-a OR b) AND (a OR -b)
	for(size_t i = 0; i < inputs1.size(); i++)
	{
		int a = 0;
		int b = 0;

		vector<int> p0;
		vector<int> p1;

		a = map1[inputs1[i]];
		b = netCount1 + map2[inputs1[i]];

		p0.push_back(-a);
		p0.push_back(b);
		cnf.push_back(p0);

		p1.push_back(a);
		p1.push_back(-b);
		cnf.push_back(p1);
	}
	//CNF for netlist1 gate
	for(size_t i = 0; i < gates1.size(); i++)
	{
		vector<int> p0;
		vector<int> p1;
		vector<int> p2;
		vector<int> p3;

		switch (gates1[i].type)
		{
			//Characteristic function of AND(a,b,c) = (a OR -c) AND (b OR -c) AND (-a OR -b OR c)
			case AND:
				p0.push_back(gates1[i].nets[0]);
				p0.push_back(-gates1[i].nets[2]);
				cnf.push_back(p0);

				p1.push_back(gates1[i].nets[1]);
				p1.push_back(-gates1[i].nets[2]);
				cnf.push_back(p1);

				p2.push_back(-gates1[i].nets[0]);
				p2.push_back(-gates1[i].nets[1]);
				p2.push_back(gates1[i].nets[2]);
				cnf.push_back(p2);
			break;
			//Characteristic function of OR(a,b,c) = (-a OR c) AND (-b OR c) AND (a OR b OR -c)
			case OR:
				p0.push_back(-gates1[i].nets[0]);
				p0.push_back(gates1[i].nets[2]);
				cnf.push_back(p0);

				p1.push_back(-gates1[i].nets[1]);
				p1.push_back(gates1[i].nets[2]);
				cnf.push_back(p1);

				p2.push_back(gates1[i].nets[0]);
				p2.push_back(gates1[i].nets[1]);
				p2.push_back(-gates1[i].nets[2]);
				cnf.push_back(p2);
			break;
			//Characteristic function of NOT(a,b) = (a OR b) AND (-a OR -b)
			case INV:
				p0.push_back(gates1[i].nets[0]);
				p0.push_back(gates1[i].nets[1]);
				cnf.push_back(p0);

				p1.push_back(-gates1[i].nets[0]);
				p1.push_back(-gates1[i].nets[1]);
				cnf.push_back(p1);
			break;
			//Characteristic function of XOR(a,b,c) = (-a OR b OR c) AND (a OR -b OR c) AND (a OR b OR -c) AND (-a OR -b OR -c)
			case XOR:
				p0.push_back(-gates1[i].nets[0]);
				p0.push_back(gates1[i].nets[1]);
				p0.push_back(gates1[i].nets[2]);
				cnf.push_back(p0);

				p1.push_back(gates1[i].nets[0]);
				p1.push_back(-gates1[i].nets[1]);
				p1.push_back(gates1[i].nets[2]);
				cnf.push_back(p1);

				p2.push_back(gates1[i].nets[0]);
				p2.push_back(gates1[i].nets[1]);
				p2.push_back(-gates1[i].nets[2]);
				cnf.push_back(p2);

				p3.push_back(-gates1[i].nets[0]);
				p3.push_back(-gates1[i].nets[1]);
				p3.push_back(-gates1[i].nets[2]);
				cnf.push_back(p3);
			break;
		}
	}

	//CNF for netlist2 gate
	for(size_t i = 0; i < gates2.size(); i++)
	{
		vector<int> p0;
		vector<int> p1;
		vector<int> p2;
		vector<int> p3;

		switch (gates2[i].type)
		{
			//Characteristic function of AND(a,b,c) = (a OR -c) AND (b OR -c) AND (-a OR -b OR c)
			case AND:
				p0.push_back(netCount1 + gates2[i].nets[0]);
				p0.push_back(-netCount1 - gates2[i].nets[2]);
				cnf.push_back(p0);

				p1.push_back(netCount1 + gates2[i].nets[1]);
				p1.push_back(-netCount1 - gates2[i].nets[2]);
				cnf.push_back(p1);

				p2.push_back(-netCount1 - gates2[i].nets[0]);
				p2.push_back(-netCount1 - gates2[i].nets[1]);
				p2.push_back(netCount1 + gates2[i].nets[2]);
				cnf.push_back(p2);
			break;
			//Characteristic function of OR(a,b,c) = (-a OR c) AND (-b OR c) AND (a OR b OR -c)
			case OR:
				p0.push_back(-netCount1 - gates1[i].nets[0]);
				p0.push_back(netCount1 + gates1[i].nets[2]);
				cnf.push_back(p0);

				p1.push_back(-netCount1 - gates1[i].nets[1]);
				p1.push_back(netCount1 + gates1[i].nets[2]);
				cnf.push_back(p1);

				p2.push_back(netCount1 + gates1[i].nets[0]);
				p2.push_back(netCount1 + gates1[i].nets[1]);
				p2.push_back(-netCount1 - gates1[i].nets[2]);
				cnf.push_back(p2);
			break;
			//Characteristic function of NOT(a,b) = (a OR b) AND (-a OR -b)
			case INV:
				p0.push_back(netCount1 + gates1[i].nets[0]);
				p0.push_back(netCount1 + gates1[i].nets[1]);
				cnf.push_back(p0);

				p1.push_back(-netCount1 - gates1[i].nets[0]);
				p1.push_back(netCount1 - gates1[i].nets[1]);
				cnf.push_back(p1);
			break;
			//Characteristic function of XOR(a,b,c) = (-a OR b OR c) AND (a OR -b OR c) AND (a OR b OR -c) AND (-a OR -b OR -c)
			case XOR:
				p0.push_back(-netCount1 - gates1[i].nets[0]);
				p0.push_back(netCount1 + gates1[i].nets[1]);
				p0.push_back(netCount1 + gates1[i].nets[2]);
				cnf.push_back(p0);

				p1.push_back(netCount1 + gates1[i].nets[0]);
				p1.push_back(-netCount1 - gates1[i].nets[1]);
				p1.push_back(netCount1 + gates1[i].nets[2]);
				cnf.push_back(p1);

				p2.push_back(netCount1 + gates1[i].nets[0]);
				p2.push_back(netCount1 + gates1[i].nets[1]);
				p2.push_back(-netCount1 - gates1[i].nets[2]);
				cnf.push_back(p2);

				p3.push_back(-netCount1 - gates1[i].nets[0]);
				p3.push_back(-netCount1 - gates1[i].nets[1]);
				p3.push_back(-netCount1 - gates1[i].nets[2]);
				cnf.push_back(p3);
			break;
		}
	}

	//Creating Miter Circuit (XORing the output of netlist1 and netlist2)
	vector<int> miter_result;
	int total_nets;
	for(size_t i = 0; i < outputs1.size(); i++)
	{
		for(size_t j = 0; j < outputs2.size(); j++)
		{
			if(outputs1[i] == outputs2[j])
			{
				//Save the output of the first circuit in miter_res1
				int miter_res1 = map1[outputs1[i]];
				//Save the output of the Second circuit in miter_res2
				int miter_res2 = map2[outputs2[j]] + netCount1;
				//Counting the total no. of outputs(OR Clause)
				int x_or = netCount1 + netCount2 + i + 1;
				//Save the output value in vector declare ad "miter_result"
				miter_result.push_back(x_or);

				vector<int> p0;
				vector<int> p1;
				vector<int> p2;
				vector<int> p3;

				p0.push_back(-(miter_res1));
				p0.push_back(miter_res2);
				p0.push_back(x_or);
				cnf.push_back(p0);

				p1.push_back(miter_res1);
				p1.push_back(-(miter_res2));
				p1.push_back(x_or);
				cnf.push_back(p1);

				p2.push_back(miter_res1);
				p2.push_back(miter_res2);
				p2.push_back(-(x_or));
				cnf.push_back(p2);

				p3.push_back(-(miter_res1));
				p3.push_back(-(miter_res2));
				p3.push_back(-(x_or));
				cnf.push_back(p3);

				total_nets = x_or;
			}
		}
	}
	cnf.push_back(miter_result);

	//for loop to check total number to clauses
	for(size_t clause = 0; clause < cnf.size(); clause++)
	{
		cout << "(";
		//For loop to check that how many literals in one clause
		for(size_t lit = 0; lit < cnf[clause].size(); lit++)
		{
			cout << cnf[clause][lit] << " ";
		}
		cout << ")";
	}

	//
	// Check CNF for satisfiability using the Davis Putnam algorithm
	//
	vector<int> value(total_nets + 1);
	DP(cnf, value);

	//
	// Print result
	//
	// ...
	
	return 0;
}
