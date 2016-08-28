#include <cstdlib>
#include<string>
#include<cstring>
#include <iostream>
#include<fstream>
#include<stdlib.h>
#include<stdio.h>
#include<sstream>
#include<map>
using namespace std;

int start_player;
int depth,task_no;
int arr_len;
int counter=0;


std::map<std::string, std::pair<std::string, std::pair<int, std::string> > > movelog;
std::map<std::string, std::pair<std::string, std::pair<int, std::string> > >::const_iterator movelogit;
std::map<string, int> nextmap;
std::map<string, int>::const_iterator nextmapit;
std::map<string, string> parmap;
std::map<string, string>::const_iterator parmapit;

void minmax_decision(int,int,int[]);
std::pair<std::string, int> minmax_val(int, int, std::map<int, std::string>);
std::map<int, std::pair<int, std::string> > gen_state(int, int[], int); //put all states generated into map with A1,B1 etc
std::pair<std::string, int> calc_util(int, int[]);
std::pair<std::string, int>find_min(std::map<std::string, int>, std::string);
std::pair<std::string, int>find_max(std::map<std::string, int>, std::string);
void writetofile(std::string, int, std::string);
void writenext(std::string);
std::string findnext(std::string, int);
std::string writenewfile(std::string, int, std::string);

void write_alphafile(std::string, int, std::string,std::string,std::string);
void write_newalphafile(std::string, int, std::string,std::string,std::string);

void alphabeta_decision(int,int,int[],std::string,std::string);
std::pair<std::string, int> alphabeta_val(int, int, std::map<int, std::string>,std::string,std::string);

void minmax_decision(int p_no,int coff,int stat[]){
    
    std::map<int, std::pair<int, std::string> > nextmove;
    std::map<int, std::pair<int, std::string> >::const_iterator nextmoveit;
	std::map<int, std::pair<int, std::string> > tempmap;
	std::map<int, std::pair<int, std::string> >::const_iterator tempit;
	std::map<int, std::pair<int, std::string> >::const_iterator parit;
    std::map<int, std::string> res;
    std::map<int, std::string>::const_iterator resit;
	std::map<std::string, int> final;
    std::map<std::string, int>::const_iterator finit;
	std::pair<std::string, int> paircheck;
	std::pair<std::string, int> pairfinal;
    char mapstate[4];
	long int li;
	std::string test;
	std::string parstate, root;
    int util,max;
    int n=(arr_len/2)-1;
	int x=0;
	writetofile("root",0,"-Infinity");
	test.clear();
	for(int i=0;i<arr_len;i++){

			test=std::to_string(stat[i]);
			parstate.append(test);
			parstate.append(" ");
	}
	parmap.insert(std::make_pair(parstate,parstate));
	test.clear();
	
	//nextmove has counter, self,state
    nextmove = gen_state(p_no,stat,coff);
	nextmoveit = nextmove.begin();
	while(nextmoveit!=nextmove.end()){
		
		movelogit=movelog.find(nextmoveit->second.second);
		 unsigned int value = 0;
		  for (int i=0;i<movelogit->second.first.size(); i++) {
			if (isdigit(movelogit->second.first[i])) {
			  value *= 10;
			  value += (movelogit->second.first[i] - '0');
		   }
		}
		
		//put in sorted map, nodename by position(2,3),self value and state string
		tempmap.insert(std::make_pair(value, std::make_pair(nextmoveit->second.first, nextmoveit->second.second)));
		nextmoveit++;
	}
	
	tempit=tempmap.begin();
	while(tempit!=tempmap.end()){
		
		movelogit=movelog.find(tempit->second.second);
		res.erase(res.begin(),res.end());
		res.insert(tempit->second);
		
		
		//start minimax value
		paircheck=minmax_val(p_no,1,res);
	
		//print it out
		final.insert(std::make_pair(tempit->second.second, paircheck.second));
		
		//find maximum
		pairfinal=find_max(final,root);
		
		test=std::to_string(pairfinal.second);
		writetofile("root",0,test);
		tempit++;
	}
	for(int i=0;i<arr_len;i++){
	
			test=std::to_string(stat[i]);
            root.append(test);
			root.append(" ");
	}

	std::string parent, nextstate;
  	
    parent.assign(pairfinal.first);
	util=pairfinal.second;
	
	tempit=tempmap.begin();
	while(tempit!=tempmap.end()){
	
      int flag=0;
      int x=0;
      while((tempit->second.second[x]) && flag==0){
      	
        	if(tempit->second.second[x]!=parent[x])
          		flag=1;
        	x++;
      	}
		if(flag==0){
			
			if(tempit->second.first==1){
			
				std::string newstate=findnext(parent, util);
            	nextstate.assign(newstate);
          	}
			else{

					nextstate.assign(parent);
          	}
		}
      tempit++;
	}

	writenext(nextstate);
}

string findnext(string parent, int util){

	std::string child, temppar, nextstat,nodeval;
	std::map<int, string> nmove;
	std::map<int, string>::const_iterator nmoveit;
	
  	parmapit=parmap.begin();
	while(parmapit!=parmap.end())
	{
			child.clear();
			temppar.clear();
			nodeval.clear();
			child.assign(parmapit->first);
			temppar.assign(parmapit->second);
      
      	int flag=0;
      	int x=0;
      	if((temppar.compare(parent)==0)){
        
			//find latest utility of the child
			child.append("\0");
			nextmapit=nextmap.find(child);

			if(nextmapit->second==util){
				
				movelogit=movelog.find(child);
				nodeval.assign(movelogit->second.first);
				std::string tempnode=nodeval.substr(1);
				int node=atoi(tempnode.c_str());
				nmove.insert(std::make_pair(node,child));
			}
		}
      parmapit++;
	}
	nmoveit=nmove.begin();
	if(nmoveit!=nmove.end()){
		
		return findnext(nmoveit->second,util);
	}

	return parent;
	
}

std::map<int, std::pair<int, std::string> > gen_state(int player, int stat[], int cutoff)
{
    int k=0,n,count=0,stones,is_max;
    int i,j,own_manc,x,val,val1,eval;
    own_manc=0;
    n=(arr_len/2)-1;
	int arr_end=arr_len-2;
	int twomanc=arr_len-1;
   
	std::string tempstate, utility;
    std::string currstate, parstate;
	const char* temp;
	const char* temp1;
    std::map<int, std::pair<int, std::string> > nmove;
    std::map<int, std::pair<int, std::string> >::const_iterator nmoveit;
    int *next_state;
    next_state = new int[arr_len];
    if(player==1){
        for(k=0;k<n;k++){
            if(stat[k]!=0){
                count++;
                //copy stat in new state
                x=0;
                while(x!=arr_len){
                    next_state[x]=stat[x];
                    x++;
                }
                i=k;
                j=i+1;
                stones=next_state[i];
                own_manc=0;
                next_state[i]=0;
                while(stones!=0){
                    if(j==arr_len-1)
                        j=0;
                    next_state[j]=next_state[j]+1;
                    j++;
                    stones--;
                }
                if(j==n+1)
                    own_manc=1;
                else if(next_state[j-1]==1){
				  if(j-1<n){
                    int x=arr_len-2;
                    int y=j-1;
                    next_state[n]=next_state[n]+next_state[y]+next_state[x-y];
                    next_state[x-y]=0;
					next_state[y]=0;
				  }
                }
                //write state to map
                currstate.clear();
                for(x=0;x!=arr_len;x++){
                
                    tempstate=std::to_string(next_state[x]);
                    currstate.append(tempstate);
					 currstate.append(" ");
                }
					
				//to return generated state, self pair
                nmove.insert(std::make_pair(count, std::make_pair(own_manc, currstate)));
					if((cutoff==depth) && (own_manc==0)){
                      
							val=next_state[n];
							val1=next_state[arr_len-1];
							
							if(start_player==1)
							eval=val-val1;
							else
							eval=val1-val;
							utility=std::to_string(eval);
					}
					else{
                                            if(player==start_player){
                                                    if(own_manc==1){
                                                            utility="-Infinity";
                                                            }
                                                    else{
                                                            utility="Infinity";
                                                    }
                                            }
                                            else{
                                                    if(own_manc==1){
                                                            utility="Infinity";
                                                            }
                                                    else{
                                                            utility="-Infinity";
                                                    }
                                            }
                                        }
					counter++;
					std::string t;
					std::string test;
					test.append("B");
					t=std::to_string(i+2);
					test.append(t);
					
					//update movelog entry for new state=state,position(B1),cutoff,utility
					movelog.insert(std::make_pair(currstate, std::make_pair(test,std::make_pair(cutoff,utility))));
					tempstate.clear();
					for(int i=0;i<arr_len;i++){
	
							tempstate=std::to_string(stat[i]);
							parstate.append(tempstate);
							parstate.append(" ");
					}
					//print parent map entry
					parmap.insert(std::make_pair(currstate,parstate));
					parstate.clear();
					
            }
        }
    }
    else{
        for(k=(arr_end);k>n;k--){
            if(stat[k]!=0){
			
                count++;
                //copy stat in new state
                x=0;
                while(x!=arr_len){
                    next_state[x]=stat[x];
                    x++;
                }
                i=k;
                j=i+1;
                stones=next_state[i];
                own_manc=0;
                next_state[i]=0;
                while(stones!=0){
					//if player 2 reached player 1's mancala, skip it
                    if(j==n)
                        j++;
					//if player 2 beyond his own mancala, loop around it to beginning
                    else if(j==arr_len)
                        j=0;
					//add the stone to destination
					int z=next_state[j];
					z++;
                    next_state[j]=z;
                    j++;
                    stones--;
                }
				j--;
                if(j==(twomanc)) // if last pit (j-1) was mancala, set flag
                    own_manc=1;
				//if last pit was empty
                else if((next_state[j])==1){	
					
					//if empty pit was his own
				  if((n<j)&&(j<twomanc)){ 	
				  
				  //empty that pit and oppnent's pit into his own mancala
                    int x=j;
                    int y=arr_len-2;
                    next_state[arr_len-1]=next_state[arr_len-1]+next_state[x]+next_state[y-x];
                    next_state[y-x]=0;
					next_state[x]=0;
				  }
                }
                currstate.clear();
                for(x=0;x!=arr_len;x++){
                
                    tempstate=std::to_string(next_state[x]);
                    currstate.append(tempstate);
					currstate.append(" ");
                }
				
				//to return generated state, self pair
                nmove.insert(std::make_pair(count, std::make_pair(own_manc, currstate)));
					if((cutoff==depth) && (own_manc==0)){
                      
							val=next_state[n];
							val1=next_state[arr_len-1];
							if(start_player==1)
							eval=val-val1;
							else
							eval=val1-val;
							utility=std::to_string(eval);
					}
					else{
                                            if(player==start_player){
                                                    if(own_manc==1){
                                                            utility="-Infinity";
                                                            }
                                                    else{
                                                            utility="Infinity";
                                                    }
                                            }
                                            else{
                                                    if(own_manc==1){
                                                            utility="Infinity";
                                                            }
                                                    else{
                                                            utility="-Infinity";
                                                    }
                                            }
                                        }
					counter++;
					std::string t1;
					std::string test1;
					test1.append("A");
					t1=std::to_string(arr_len-i);
					test1.append(t1);
					
					//update movelog entry for new state=state,position(A1),cutoff,utility
					movelog.insert(std::make_pair(currstate, std::make_pair(test1,std::make_pair(cutoff,utility))));
					tempstate.clear();
					for(int i=0;i<arr_len;i++){
	
							tempstate=std::to_string(stat[i]);
							parstate.append(tempstate);
							parstate.append(" ");
					}
					
					//print parent map entry
					parmap.insert(std::make_pair(currstate,parstate));
					parstate.clear();
            }
        }
    }
   return nmove; 
}

std::pair<std::string, int> minmax_val(int player, int coff, std::map<int, std::string> mapval){
	
	int x, stat[arr_len], max, flag=0, opp_player;
	int n=(arr_len)/2;
	const char* temp;
	char* trial;
	bool checkcut=false;
	std::map<int, std::string>::const_iterator mapit;
	std::map<int, std::pair<int, std::string> > result;
	std::map<int, std::pair<int, std::string> >::const_iterator resultit;
	std::map<int, std::string> list_results;
	std::map<int, std::string>::const_iterator listit;
	std::map<std::string, int> final_list;
	std::pair<std::string, int> check;
	std::pair<std::string, int> checkfin;
	std::pair<std::string, int> checktemp;
	std::pair<std::string, int> temputil;
	std::map<std::string, int>::const_iterator finit;
	std::map<int, std::pair<int, std::string> > tempmap;
	std::map<int, std::pair<int, std::string> >::const_iterator tempit;
	mapit=mapval.begin();
	int count=0;
	std::string node,node_char;
	std::stringstream ss;
	ss<<mapit->second;
		while ( getline( ss, node, ' ' ) ) {
			stat[count]=atoi(node.c_str());
			//cout<<stat[count];
            node.clear();
			count++;
		}
  	ss.clear();
	
		for(int counter=0;counter<(n-1);counter++){
			if(stat[counter]==0)
				flag++;
		}
		if(flag==(n-1)){
			
			for(int counter=n;counter<(arr_len-1);counter++){
					stat[arr_len-1]=stat[arr_len-1]+stat[counter];
					stat[counter]=0;
			}
			temputil=calc_util(player, stat);
			movelogit=movelog.find(mapit->second);
			std::string test;
			test=std::to_string(temputil.second);
			writetofile(movelogit->second.first,movelogit->second.second.first,test);
			return(temputil);
		}
		
		flag=0;
		for(int counter=(arr_len/2);counter<(arr_len-1);counter++){
			if(stat[counter]==0)
			flag++;
		}
		if(flag==(n-1)){
		                                              
			for(int counter=0;counter<(n-1);counter++){
					stat[n-1]=stat[n-1]+stat[counter];
					stat[counter]=0;
			}
			
			temputil=calc_util(player, stat);
			movelogit=movelog.find(mapit->second);
			std::string test;
			test=std::to_string(temputil.second);
			writetofile(movelogit->second.first,movelogit->second.second.first,test);
			return(temputil);
		}
	
	if(coff==depth && mapit->first==0){
				
		temputil=calc_util(player, stat);
		movelogit=movelog.find(mapit->second);
		std::string test;
		test=std::to_string(temputil.second);
		writetofile(movelogit->second.first,movelogit->second.second.first,test);
		
		if(task_no==1){
		
			if(player==start_player && coff==1){
			
				//insert latest value in map
				nextmap.insert(std::make_pair(mapit->second,temputil.second));
			}
		}
		
		return(temputil);
	}
	if(mapit->first==1){
		result=gen_state(player, stat,coff);
	}
	else{
		if(coff==1){
				
				checkcut=true;
		}
		coff++;
		if(player==1)
			opp_player=2;
		else
			opp_player=1;
		result=gen_state(opp_player, stat,coff);
	}
	resultit=result.begin();
	while(resultit!=result.end()){
		
		movelogit=movelog.find(resultit->second.second);
		 unsigned int value = 0;
		  for (int i=0;i<movelogit->second.first.size(); i++) {
			if (isdigit(movelogit->second.first[i])) {
			  value *= 10;
			  value += (movelogit->second.first[i] - '0');
		   }
		}
		tempmap.insert(std::make_pair(value, std::make_pair(resultit->second.first, resultit->second.second)));
		resultit++;
	}
	
	movelogit=movelog.find(mapit->second);
	writetofile(movelogit->second.first,movelogit->second.second.first,movelogit->second.second.second);
	tempit=tempmap.begin();
	while(tempit!=tempmap.end()){	
			
			list_results.erase(list_results.begin(),list_results.end());
			list_results.insert(tempit->second);
			if(mapit->first==1)
				checktemp=minmax_val(player,coff,list_results);
			else
				checktemp=minmax_val(opp_player,coff,list_results);
			checkfin=std::make_pair(tempit->second.second,checktemp.second);
			final_list.insert(checkfin);
			if(player==start_player){
			
				if(mapit->first==1){
	
					check=find_max(final_list, mapit->second);	
					std::string test1;
					test1=std::to_string(check.second);
                  	movelogit=movelog.find(mapit->second);
					writetofile(movelogit->second.first,movelogit->second.second.first,test1);
				}
				else{
					
					check=find_min(final_list, mapit->second);
					std::string test2;
					test2=std::to_string(check.second);
                  	movelogit=movelog.find(mapit->second);
					writetofile(movelogit->second.first,movelogit->second.second.first,test2);
				}
			}
			else{
			
				if(mapit->first==1){
				
					check=find_min(final_list, mapit->second);
					std::string test2;
					test2=std::to_string(check.second);
                  	movelogit=movelog.find(mapit->second);
					writetofile(movelogit->second.first,movelogit->second.second.first,test2);
				}
				else{
				
					check=find_max(final_list, mapit->second);
					std::string test1;
					test1=std::to_string(check.second);
                  	movelogit=movelog.find(mapit->second);
					writetofile(movelogit->second.first,movelogit->second.second.first,test1);
				}
			}
			++tempit;
		}
		if(player==start_player && (coff==1 || checkcut==true)){
			
				//insert latest value in map
				nextmap.insert(std::make_pair(mapit->second, check.second));
		}
		
		if(player==start_player && (mapit->first!=1 || checkcut==true || coff==1))
		{
			nextmapit=nextmap.find(mapit->second);
			check=std::make_pair(mapit->second,nextmapit->second);
		
		}
	return check;
}


std::pair<std::string, int> calc_util(int player, int stat[]){

	int util,n;
	std::string state;
	std::string tempstate;
	n=(arr_len/2)-1;
	if(start_player==1)
		util=stat[n]-stat[arr_len-1];
	else
		util=stat[arr_len-1]-stat[n];
	for(int i=0;i<arr_len;i++){
	
			tempstate=std::to_string(stat[i]);
            state.append(tempstate);
			 state.append(" ");
	}
	movelogit=movelog.find(state);
	return(std::make_pair(state,util));
}

std::pair<std::string, int>find_min(std::map<std::string, int> final_list, std::string parent){
	
	std::map<std::string, int>::const_iterator finit;
	int min,x;
	int minnode;
	std::string finstate;
	std::map<int, std::pair<std::string, int> > tempmap;
	std::map<int, std::pair<std::string, int> >::const_iterator tempit;
	finit=final_list.begin();
	
	while(finit!=final_list.end()){
		movelogit=movelog.find(finit->first);
		 unsigned int value = 0;
		  for (int i=0;i<movelogit->second.first.size(); i++) {
			if (isdigit(movelogit->second.first[i])) {
			  value *= 10;
			  value += (movelogit->second.first[i] - '0');
		   }
		}
		tempmap.insert(std::make_pair(value, std::make_pair(finit->first, finit->second)));
		finit++;
	}
	
	//change this later
		tempit=tempmap.begin();
		min=tempit->second.second;
		finstate.assign(tempit->second.first);
		while(tempit!=tempmap.end()){
			if(min>tempit->second.second){
				min=tempit->second.second;
				finstate.clear();
				finstate.assign(tempit->second.first);
			}
			tempit++;
		}
	return(std::make_pair(finstate,min));
}

std::pair<std::string, int>find_max(std::map<std::string, int> final_list, std::string parent){
	
	std::map<std::string, int>::const_iterator finit;
	int max;
	int maxnode;
	std::string finstate;
	std::map<int, std::pair<std::string, int> > tempmap;
	std::map<int, std::pair<std::string, int> >::const_iterator tempit;
	finit=final_list.begin();
	//sort final_list on state name
	
	while(finit!=final_list.end()){
		
		movelogit=movelog.find(finit->first);
		 unsigned int value = 0;
		  for (int i=0;i<movelogit->second.first.size(); i++) {
			if (isdigit(movelogit->second.first[i])) {
			  value *= 10;
			  value += (movelogit->second.first[i] - '0');
		   }
		}
		tempmap.insert(std::make_pair(value, std::make_pair(finit->first, finit->second)));
		finit++;
	}
	
	//change this later
		tempit=tempmap.begin();
		max=tempit->second.second;
		finstate.assign(tempit->second.first);
		while(tempit!=tempmap.end()){
			if(max<tempit->second.second){
				max=tempit->second.second;
				finstate.clear();
				finstate.assign(tempit->second.first);
			}
			tempit++;
		}
	return(std::make_pair(finstate,max));
}

void writetofile(std::string nodename, int depth, std::string util){

	if(task_no!=1){
		ofstream outfile("traverse_log.txt", ios::app);
		std::string op;
		std::string temp;
		op.append(nodename);
		op.append(",");
		if(depth==111111)
			op.append("Depth");
		else{
			temp=std::to_string(depth);
			op.append(temp);
		}
		op.append(",");
		op.append(util);
		if (outfile.is_open()){
			
				outfile<<op;
				outfile<<endl;
		}
		else
			std::cout<<"Could not open output file!";
		outfile.close();
	}	
}

void writenext(string nmove){

	ofstream outnexfile("next_state.txt");
	
	std::string n2,m2,n1,m1;
	int count=0;
	int n=(arr_len/2)-1;
	std::string node,node_char;
	std::stringstream ss;
	ss<<nmove;
	if (outnexfile.is_open()){
		
		while ( getline( ss, node, ' ' ) ) {
				
			if(count<(arr_len/2)){
				if(count<(n-1)){
					n1.append(node);
					n1.append(" ");
					count++;
				}
              
				else if(count==(n-1)){
				
					n1.append(node);
					count++;
				}
				else if(count==n){
					m1.append(node);
					count++;
				}
			}
			else if(count>=(arr_len/2) && count<arr_len){
			
				if(count<(arr_len-2)){
					n2.append(node);
					n2.append(" ");
					count++;
				}
				else if(count==(arr_len-2)){
				
					n2.append(node);
					count++;
				}
				else if(count==arr_len-1){
					m2.append(node);
					count++;
				}
			}	
          	node.clear();
		}
      	
		for (std::string::reverse_iterator rit=n2.rbegin(); rit!=n2.rend(); ++rit)
   			 outnexfile<<*rit;
		outnexfile<<endl;
		outnexfile<<n1;
		outnexfile<<endl;
		outnexfile<<m2;
		outnexfile<<endl;
		outnexfile<<m1;
	}
	else
		std::cout<<"Could not open output next file!";
	outnexfile.close();	
}

string writenewfile(std::string nodename, int depth, std::string util){

	ofstream onewfile("traverse_log.txt");
  
	std::string op;
	std::string temp;
	op.append(nodename);
	op.append(",");
	if(depth==111111)
		op.append("Depth");
	else{
		temp=std::to_string(depth);
		op.append(temp);
	}
	op.append(",");
	op.append(util);
	if (onewfile.is_open()){
		
			onewfile<<op;
			onewfile<<endl;
	}
	else
		std::cout<<"Could not open output file!";
	onewfile.close();

}


void write_newalphafile(std::string nodename, int depth, std::string util, std::string alph, std::string bet){

	ofstream outnewfile("traverse_log.txt");
	
	std::string op;
	std::string temp;
	op.append(nodename);
	op.append(",");
	if(depth==111111)
		op.append("Depth");
	else{
		temp=std::to_string(depth);
		op.append(temp);
	}
	op.append(",");
	op.append(util);
	op.append(",");
	op.append(alph);
	op.append(",");
	op.append(bet);
	if (outnewfile.is_open()){
		
			outnewfile<<op;
			outnewfile<<endl;
	}
	else
		std::cout<<"Could not open output file!";
	outnewfile.close();

}


void write_alphafile(std::string nodename, int depth, std::string util,std::string alph,std::string bet){

	if(task_no!=1){
		ofstream outfile("traverse_log.txt",ios::app);
		std::string op;
		std::string temp;
		op.append(nodename);
		op.append(",");
		if(depth==111111)
			op.append("Depth");
		else{
			temp=std::to_string(depth);
			op.append(temp);
		}
		op.append(",");
		op.append(util);
      	op.append(",");
		op.append(alph);
		op.append(",");
		op.append(bet);
		if (outfile.is_open()){
			
				outfile<<op;
				outfile<<endl;
		}
		else
			std::cout<<"Could not open output file!";
		outfile.close();
	}	
}



std::pair<std::string, int> alphabeta_val(int player, int coff, std::map<int, std::string> mapval,std::string alpha,std::string beta){

	int x, stat[arr_len], max, flag=0, opp_player;
	int n=(arr_len)/2;
	const char* temp;
	char* trial;
	bool checkcut=false;
	std::map<int, std::string>::const_iterator mapit;
	std::map<int, std::pair<int, std::string> > result;
	std::map<int, std::pair<int, std::string> >::const_iterator resultit;
	std::map<int, std::string> list_results;
	std::map<int, std::string>::const_iterator listit;
	std::map<std::string, int> final_list;
	std::pair<std::string, int> check;
	std::pair<std::string, int> checkfin;
	std::pair<std::string, int> checktemp;
	std::pair<std::string, int> temputil;
	std::map<std::string, int>::const_iterator finit;
	std::map<int, std::pair<int, std::string> > tempmap;
	std::map<int, std::pair<int, std::string> >::const_iterator tempit;
	mapit=mapval.begin();
	int count=0;
	std::string node,node_char;
	std::stringstream ss;
	ss<<mapit->second;
		while ( getline( ss, node, ' ' ) ) {
			stat[count]=atoi(node.c_str());
            node.clear();
			count++;
		}
  	ss.clear();
	
	if(player==1){
		for(int counter=0;counter<(n-1);counter++){
			if(stat[counter]==0)
				flag++;
		}
		if(flag==(n-1)){
			
			for(int counter=n;counter<(arr_len-1);counter++){
					stat[arr_len-1]=stat[arr_len-1]+stat[counter];
					stat[counter]=0;
			}
			temputil=calc_util(player, stat);
			movelogit=movelog.find(mapit->second);
			std::string test;
			test=std::to_string(temputil.second);
			write_alphafile(movelogit->second.first,movelogit->second.second.first,test,alpha,beta);
			return(temputil);
		}
	}
	else{
		
		for(int counter=(arr_len/2);counter<arr_len;counter++){
			if(stat[counter]==0)
			flag++;
		}
		if(flag==(n-1)){
		                                              
			for(int counter=0;counter<(n-1);counter++){
					stat[n-1]=stat[n-1]+stat[counter];
					stat[counter]=0;
			}
			
			temputil=calc_util(player, stat);
			movelogit=movelog.find(mapit->second);
			std::string test;
			test=std::to_string(temputil.second);
			write_alphafile(movelogit->second.first,movelogit->second.second.first,test,alpha,beta);
		
			return(temputil);
		}
	}
	
	if(coff==depth && mapit->first==0){
				
		temputil=calc_util(player, stat);
		movelogit=movelog.find(mapit->second);
		std::string test;
		test=std::to_string(temputil.second);
		write_alphafile(movelogit->second.first,movelogit->second.second.first,test,alpha,beta);
		
		if(task_no==1){
		
			if(player==start_player && coff==1){
			
				//insert latest value in map
				nextmap.insert(std::make_pair(mapit->second,temputil.second));
			}
		}
		
		return(temputil);
	}
	if(mapit->first==1){
		result=gen_state(player, stat,coff);
	}
	else{
		if(coff==1){
				
				checkcut=true;
		}
		coff++;
		if(player==1)
			opp_player=2;
		else
			opp_player=1;
		result=gen_state(opp_player, stat,coff);
	}
	resultit=result.begin();
	while(resultit!=result.end()){
		
		movelogit=movelog.find(resultit->second.second);
		 unsigned int value = 0;
		  for (int i=0;i<movelogit->second.first.size(); i++) {
			if (isdigit(movelogit->second.first[i])) {
			  value *= 10;
			  value += (movelogit->second.first[i] - '0');
		   }
		}
		tempmap.insert(std::make_pair(value, std::make_pair(resultit->second.first, resultit->second.second)));
		resultit++;
	}
	
	movelogit=movelog.find(mapit->second);
	write_alphafile(movelogit->second.first,movelogit->second.second.first,movelogit->second.second.second,alpha,beta);
	tempit=tempmap.begin();
	while(tempit!=tempmap.end()){	
			
			list_results.erase(list_results.begin(),list_results.end());
			list_results.insert(tempit->second);
			if(mapit->first==1)
				checktemp=alphabeta_val(player,coff,list_results,alpha,beta);
			else
				checktemp=alphabeta_val(opp_player,coff,list_results,alpha,beta);
			checkfin=std::make_pair(tempit->second.second,checktemp.second);
			final_list.insert(checkfin);
			if(player==start_player){
			
				if(mapit->first==1){
				
					//Find MAXIMUM of self moves
					check=find_max(final_list, mapit->second);	
					std::string test2;
					int alphaint,betaint,is_inf=1,is_neginf=1;
					is_neginf=alpha.compare("-Infinity");
					is_inf=beta.compare("Infinity");
					test2=std::to_string(check.second);
					std::string talpha;
					talpha.assign(alpha);
					//update alpha values
					if(is_neginf==0){
					
						alpha.clear();
						alpha.assign(test2);
					}
					else{
						
						alphaint=atoi(alpha.c_str());
						if(check.second>alphaint){
						
							alpha.clear();
							alpha.assign(test2);
						}
					}
					is_neginf=alpha.compare("-Infinity");
					//return beta values
					if(is_inf!=0 && is_neginf!=0){
						betaint=atoi(beta.c_str());
						alphaint=atoi(alpha.c_str());
						if(betaint<=alphaint){
						
							check.second=betaint;
                          movelogit=movelog.find(mapit->second);
							write_alphafile(movelogit->second.first,movelogit->second.second.first,test2,talpha,beta);
							return check;
						}
					}
		
					
                  	movelogit=movelog.find(mapit->second);
					write_alphafile(movelogit->second.first,movelogit->second.second.first,test2,alpha,beta);
				}
				else{
				
				//Find MINIMUM of opponent's moves
					check=find_min(final_list, mapit->second);
					std::string test2;
					int alphaint,betaint,is_inf=1,is_neginf=1;
					is_neginf=alpha.compare("-Infinity");
					is_inf=beta.compare("Infinity");
					test2=std::to_string(check.second);
					std::string tbeta;
					tbeta.assign(beta);
					//update beta value
					if(is_inf==0){
					
						beta.clear();
						beta.assign(test2);
					}
					else{
						
						betaint=atoi(beta.c_str());
						if(check.second<betaint){
						
							beta.clear();
							beta.assign(test2);
						}
					}
					is_inf=beta.compare("Infinity");
					//return alpha value
					if(is_inf!=0 && is_neginf!=0){
						alphaint=atoi(alpha.c_str());
						betaint=atoi(beta.c_str());
						if(betaint<=alphaint){
						
							check.second=alphaint;
                          movelogit=movelog.find(mapit->second);
							write_alphafile(movelogit->second.first,movelogit->second.second.first,test2,alpha,tbeta);
							return check;
						}
					}
					
                  	movelogit=movelog.find(mapit->second);
					write_alphafile(movelogit->second.first,movelogit->second.second.first,test2,alpha,beta);
				}
			}
			else{
			
				if(mapit->first==1){
				//Find MINIMUM of self moves
					check=find_min(final_list, mapit->second);
					std::string test2;
					int alphaint,betaint,is_inf=1,is_neginf=1;
					is_neginf=alpha.compare("-Infinity");
					is_inf=beta.compare("Infinity");
					test2=std::to_string(check.second);
					std::string tbeta;
					tbeta.assign(beta);
					
					//update beta value
					if(is_inf==0){
					
						beta.clear();
						beta.assign(test2);
					}
					else{
						
						betaint=atoi(beta.c_str());
						if(check.second<betaint){
						
							beta.clear();
							beta.assign(test2);
						}
					}
					is_inf=beta.compare("Infinity");
					//return alpha value
					if(is_inf!=0 && is_neginf!=0){
						alphaint=atoi(alpha.c_str());
						betaint=atoi(beta.c_str());
						if(betaint<=alphaint){
						
							check.second=alphaint;
                          	movelogit=movelog.find(mapit->second);
							write_alphafile(movelogit->second.first,movelogit->second.second.first,test2,alpha,tbeta);
							return check;
						}
					}
					
                  	movelogit=movelog.find(mapit->second);
					write_alphafile(movelogit->second.first,movelogit->second.second.first,test2,alpha,beta);
				}
				else{
					
				//Find MAXIMUM of start's moves
					check=find_max(final_list, mapit->second);
					std::string test2;
					int alphaint,betaint,is_inf=1,is_neginf=1;
					is_neginf=alpha.compare("-Infinity");
					is_inf=beta.compare("Infinity");
					test2=std::to_string(check.second);
					std::string talpha;
					talpha.assign(alpha);
					//update alpha values
					if(is_neginf==0){
					
						alpha.clear();
						alpha.assign(test2);
					}
					else{
						
						alphaint=atoi(alpha.c_str());
						if(check.second>alphaint){
						
							alpha.clear();
							alpha.assign(test2);
						}
					}
					is_neginf=alpha.compare("-Infinity");
					//return beta values
					if(is_inf!=0 && is_neginf!=0){
						betaint=atoi(beta.c_str());
						alphaint=atoi(alpha.c_str());
						if(betaint<=alphaint){
						
							check.second=betaint;
                          movelogit=movelog.find(mapit->second);
							write_alphafile(movelogit->second.first,movelogit->second.second.first,test2,talpha,beta);
							return check;
						}
					}
		
                  	movelogit=movelog.find(mapit->second);
					write_alphafile(movelogit->second.first,movelogit->second.second.first,test2,alpha,beta);
				}
			}
			++tempit;
		}
		if(player==start_player && (coff==1 || checkcut==true)){
			
				//insert latest value in map
				nextmap.insert(std::make_pair(mapit->second, check.second));
		}
		
		if(player==start_player && (mapit->first!=1 || checkcut==true || coff==1))
		{
			nextmapit=nextmap.find(mapit->second);
			check=std::make_pair(mapit->second,nextmapit->second);
		
		}
	return check;
}

void alphabeta_decision(int p_no,int coff,int stat[],std::string alpha,std::string beta){
    
    std::map<int, std::pair<int, std::string> > nextmove;
    std::map<int, std::pair<int, std::string> >::const_iterator nextmoveit;
	std::map<int, std::pair<int, std::string> > tempmap;
	std::map<int, std::pair<int, std::string> >::const_iterator tempit;
	std::map<int, std::pair<int, std::string> >::const_iterator parit;
    std::map<int, std::string> res;
    std::map<int, std::string>::const_iterator resit;
	std::map<std::string, int> final;
    std::map<std::string, int>::const_iterator finit;
	std::pair<std::string, int> paircheck;
	std::pair<std::string, int> pairfinal;
    char mapstate[4];
	long int li;
	std::string test;
	std::string parstate, root;
    int util,max;
    int n=(arr_len/2)-1;
	int x=0;
	//std::cout<<"Root,0,I-nfinity";
	write_alphafile("root",0,"-Infinity","-Infinity","Infinity");
	test.clear();
	for(int i=0;i<arr_len;i++){

			test=std::to_string(stat[i]);
			parstate.append(test);
			parstate.append(" ");
	}
	parmap.insert(std::make_pair(parstate,parstate));
	test.clear();
	
	//nextmove has counter, self,state
    nextmove = gen_state(p_no,stat,coff);
	nextmoveit = nextmove.begin();
	while(nextmoveit!=nextmove.end()){
		
		movelogit=movelog.find(nextmoveit->second.second);
		 unsigned int value = 0;
		  for (int i=0;i<movelogit->second.first.size(); i++) {
			if (isdigit(movelogit->second.first[i])) {
			  value *= 10;
			  value += (movelogit->second.first[i] - '0');
		   }
		}
		
		//put in sorted map, nodename by position(2,3),self value and state string
		tempmap.insert(std::make_pair(value, std::make_pair(nextmoveit->second.first, nextmoveit->second.second)));
		nextmoveit++;
	}
	
	tempit=tempmap.begin();
	while(tempit!=tempmap.end()){
		
		movelogit=movelog.find(tempit->second.second);
		res.erase(res.begin(),res.end());
		res.insert(tempit->second);
		
		//start minimax value
		std::string inf, neginf;
		paircheck=alphabeta_val(p_no,1,res,alpha,beta);
	
		//print it out
		final.insert(std::make_pair(tempit->second.second, paircheck.second));
		
		//find maximum
		pairfinal=find_max(final,root);
		
		test=std::to_string(pairfinal.second);	
		int alphaint,betaint,is_inf=1,is_neginf=1;
		is_neginf=alpha.compare("-Infinity");
		is_inf=beta.compare("Infinity");
		
		//update alpha value
		if(is_neginf==0){
		
			alpha.clear();
			alpha.assign(test);
		}
		else{
			
			alphaint=atoi(alpha.c_str());
			if(pairfinal.second>alphaint){
			
				alpha.clear();
				alpha.assign(test);
			}
		}
		
		write_alphafile("root",0,test,alpha,beta);
		tempit++;
	}
	for(int i=0;i<arr_len;i++){
	
			test=std::to_string(stat[i]);
            root.append(test);
			root.append(" ");
	}

	std::string parent, nextstate;
  	
    parent.assign(pairfinal.first);
	util=pairfinal.second;
	
	tempit=tempmap.begin();
	while(tempit!=tempmap.end()){
	
      int flag=0;
      int x=0;
      while((tempit->second.second[x]) && flag==0){
      	
        	if(tempit->second.second[x]!=parent[x])
          		flag=1;
        	x++;
      	}
		if(flag==0){
			
			if(tempit->second.first==1){
			
				std::string newstate=findnext(parent, util);
            		nextstate.assign(newstate);
          	}
			else{
            
					nextstate.assign(parent);
          	}
		}
      tempit++;
	}
	writenext(nextstate);
}




int main(int argc, char** argv) {
    
    ifstream infile(argv[2]);
    std::string line,node,node_char;
    int player_no;
    int len,n,i,j,k;
	std::string test,test1,teststat;
    std::stringstream ss;
    /*Read input file from command line*/
    if(infile.is_open()==false)
            std::cout<<"\ncould not open file";
    else{

        getline(infile,line);
        task_no=atoi(line.c_str());
        getline(infile,line);
        player_no=atoi(line.c_str());
        start_player=player_no;
        getline(infile,line);
        depth=atoi(line.c_str());
		if(task_no==1)
			depth=1;
        getline(infile,line);
        len=line.size();
        n=(len+1)/2;
        arr_len=(2*n)+2;
        int *state;
        state = new int[arr_len];
        //read player 2's board state
        i=0;
		j=1;
        int count=arr_len-2;
        node.clear();
        while(j<=n){
			node.clear();
            while(isdigit(line[i])){
                ss.clear();
                node_char.clear();
                ss<<line[i];
                ss>>node_char;
                node.append(node_char);
                i++;
            }
			i++;
            state[count]=atoi(node.c_str());
            count--;
			j++;
        }
        getline(infile,line);
        i=0;
		k=1;
        node.clear();
        while(k<=n){
			node.clear();
            while(isdigit(line[i])){
                ss.clear();
                node_char.clear();
                ss<<line[i];
                ss>>node_char;
                node.append(node_char);
                i++;
            }
			i++;
            state[k-1]=atoi(node.c_str());
			k++;
        }
        getline(infile,line);
        state[arr_len-1]=atoi(line.c_str());
        getline(infile,line);
        state[n]=atoi(line.c_str());
		
		std::string utility="Infinity";
		test="Root";
		int coff=0;
		std::string statestr;
		for(int k=0;k<arr_len;k++){
	
			teststat=std::to_string(state[k]);
            statestr.append(teststat);
			statestr.append(" ");
		}
		movelog.insert(std::make_pair(statestr,std::make_pair(test,std::make_pair(coff,utility))));
		if(task_no==1)
			minmax_decision(player_no,1,state);
		else if(task_no==2){
			writenewfile("Node",111111,"Value");
			minmax_decision(player_no,1,state);
		}
		else if(task_no==3){
		
			std::string inf,neginf;
			inf.assign("Infinity");
			neginf.assign("-Infinity");
			write_newalphafile("Node",111111,"Value","Alpha","Beta");
          	alphabeta_decision(player_no,1,state,neginf,inf);
		}
    }  
	infile.close();
	return 0;
}