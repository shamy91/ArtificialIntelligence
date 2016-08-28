package asm3;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.StringTokenizer;

public class testFOL {

	public static Map<Integer, String> rhsclause = new HashMap<Integer, String>();
	public static Map<Integer, String> lhsclause = new HashMap<Integer, String>();
	public static Map<Integer, String> facts = new HashMap<Integer, String>();
	public static Map<String,Integer> occurs = new HashMap<String, Integer>();
	public static Map<String,Integer> rhsoccurs = new HashMap<String, Integer>();
	public static List<String> entailed = new ArrayList<String>();
	public static Integer gcount =0;
	
	public static void main(String[] args) {
		

		int queries, clauses;
		List<String> querylist = new ArrayList<String>();
		List<String> clauselist = new ArrayList<String>();
		//System.out.println("Hello world");
		
		File inFile = null;
		if (0 < args.length) {
		  
	        
			inFile = new File(args[0]);
			BufferedReader br = null;
			BufferedWriter bufWriter = null;
		    try {
		    	
			    bufWriter = new BufferedWriter(new FileWriter("output.txt"));
		        
			    String sCurrentLine = null;
		        br = new BufferedReader(new FileReader(inFile));
		        
		        //Read number of queries
		        sCurrentLine = br.readLine();
		        queries = Integer.parseInt(sCurrentLine);
		        
		        //collect all queries
		        while(queries!=0){
		        	
		        	sCurrentLine = br.readLine();	
		        	querylist.add(sCurrentLine);
		        	queries--;
		        }
		        
		        //Read number of clauses in KB
		        sCurrentLine = br.readLine();
		        clauses = Integer.parseInt(sCurrentLine);
		        
		      //collect all clauses
		        while(clauses!=0){
		        	
		        	sCurrentLine = br.readLine();	
		        	clauselist.add(sCurrentLine);
		        	clauses--;
		        }
		        
		        //Split all clauses and store
		        for (int i=0;i < clauselist.size();i++)
		        {
		        	splitclause(clauselist.get(i), i);
		        }
		        
		        //Count occurrence of each predicate in facts
		        for (Map.Entry<Integer, String> entry : facts.entrySet()){
		        
		        	StringTokenizer str = new StringTokenizer(entry.getValue(), "("); 
		    		String factpred = str.nextToken().trim();
		        	Integer count = occurs.get(factpred);
		        	count++;
		        	occurs.remove(factpred);
		        	occurs.put(factpred, count);
		        }
		        
		        //Count occurrence of each predicate in RHS
		        for (Map.Entry<Integer, String> entry : rhsclause.entrySet()){
		        
		        	StringTokenizer str = new StringTokenizer(entry.getValue(), "("); 
		    		String factpred = str.nextToken().trim();
		        	Integer count = rhsoccurs.get(factpred);
		        	count++;
		        	rhsoccurs.remove(factpred);
		        	rhsoccurs.put(factpred, count);
		        }
		        
		        //for each query, check if it is true
		        for (int i=0;i < querylist.size();i++)
		        {
		        	
		        		if(entailed.isEmpty()==false){
		        			entailed.clear();
		        		}
		        		List<String> qlist = new ArrayList<String>();
		        		qlist.add(querylist.get(i));
		        		Map<String,String> thetafinal = new HashMap<String,String>();
		        		thetafinal.put(" ", " ");
		        		thetafinal.clear();
		        		List<Map<String,String>> checklist = back_chain(qlist,thetafinal);
			        	if(checklist.isEmpty()==false){
			        		
			        		System.out.println("TRUE");
			        		bufWriter.write("TRUE"+"\n");
			        	}
			        	else{
			        		
			        		System.out.println("FALSE");
			        		bufWriter.write("FALSE"+"\n");
			        	}
		        	
		        }
		        bufWriter.close();
		        br.close();
		    } 
		    catch (IOException e) {
		      
		    	e.printStackTrace();
		    } 
		} 
		else {
		  
			System.err.println("Invalid arguments count:" + args.length);
		
		}
	}

private static List<Map<String, String>> back_chain(List<String> querylist,Map<String, String> thetamap) {
		
	List<String> qlist = new ArrayList<String>();
	Map<String, String> theta = new HashMap<String,String>();
	qlist.addAll(querylist);
	theta.putAll(thetamap);
	List<Map<String,String>> answers = new ArrayList<Map<String,String>>();
	List<Map<String,String>> factmatchlist = new ArrayList<Map<String,String>>();
	Map<Integer,String> rhslist = new HashMap<Integer,String>();
	if(qlist.isEmpty()){
		
		answers.add(theta);
		return answers;
	}
	String query = qlist.get(0); 
	String pred = give_pred(query);
	if(entailed.contains(query)){
		
		theta.clear();
		answers.add(theta);
		answers.clear();
		return answers;
	}
	
	if(checkforfact(query)==true){
		entailed.add(query);
	}
	//check if it is a known fact
	if(facts.containsValue(query)==true){
		
		Map<String,String> facttheta = new HashMap<String,String>();
		String termstr = get_termstring(query);
		List<String> terms = get_terms(termstr);
		for(int i=0;i<terms.size();i++){
			
				facttheta.put(terms.get(i), terms.get(i));
			
		}
		theta.putAll(facttheta);
		answers.add(theta);
	}
	
	//check partial match with fact and get thetadash
	if(occurs.containsKey(pred)){
		
		factmatchlist = check_part_fact(query, theta);
		if(factmatchlist.isEmpty()==false){
			for(int k=0;k<factmatchlist.size();k++){
				
				if(answers.contains(factmatchlist.get(k))==false){
					
					answers.add(factmatchlist.get(k));
				}
			}
		}
	}	
	
	//check if it is in RHS of an implication
	if(rhsoccurs.containsKey(pred)){
	    
		for (Map.Entry<Integer, String> entry : rhsclause.entrySet()) {
    		
    		String clause = entry.getValue();
    		StringTokenizer str = new StringTokenizer(clause, "("); 
    		String rhspred = str.nextToken().trim();
    		if(pred.equals(rhspred)== true){
    		
    			rhslist.put(entry.getKey(), entry.getValue());
    		}
    	}
	}
	
thisloop:	for(Map.Entry<Integer, String> thisentry: rhslist.entrySet()){
		
		List<Map<String,String>> tempanswers = new ArrayList<Map<String,String>>();
		Map<String,String> testmap = new HashMap<String,String>();
		Map<String, String> thetanew = new HashMap<String,String>();
		thetanew.putAll(theta);
		String teststand = standardize(thisentry.getValue(),gcount);
		testmap = compose(query,teststand,theta);
		if(testmap.isEmpty()){
			
			continue;
		}
		thetanew.putAll(testmap);
		//answers.add(thetanew);
		String leftlist= lhsclause.get(thisentry.getKey());
		List<String> subs_list = new ArrayList<String>();
		if(leftlist!=null){
			//get all lhs clauses
			List<String> newcllist = split_conj(leftlist);
			for(int i=0;i<newcllist.size();i++){
				
				String teststandlhs = standardize(newcllist.get(i),gcount);
				String sublist = substitute(teststandlhs,thetanew);
				subs_list.add(sublist);
			}
			gcount++;
			tempanswers = back_chain(subs_list,thetanew);
			if(tempanswers.isEmpty()==false){
				for(int count=0;count<tempanswers.size();count++){
					
					if(answers.contains(tempanswers.get(count))==false){
						answers.add(tempanswers.get(count));
					}
				}
			}
		}
		if(tempanswers.isEmpty()==false){
			
			break thisloop;
		}
	}

	List<Map<String,String>> newanswers = new ArrayList<Map<String,String>>();
	if(qlist.isEmpty()==false && qlist.size()>1){
		qlist.remove(0);
		List<Map<String,String>> testanswers = new ArrayList<Map<String,String>>();
		for(int k=0;k<answers.size();k++){
				Map<String,String> thisans = new HashMap<String,String>();
				thisans = answers.get(k);
				testanswers = back_chain(qlist,thisans);
				if(testanswers.isEmpty()==false){
					if(newanswers.contains(testanswers)==false){
						newanswers.addAll(testanswers);
					}
				}
		}
		return newanswers;
	}
	return answers;
}

public static boolean checkforfact(String clause){
	
	String str = get_termstring(clause);
	List<String> fact_terms = get_terms(str); 
	for(int ct=0;ct<fact_terms.size();ct++){
		
		if(Character.isLowerCase(fact_terms.get(ct).charAt(0))){
			return false;
		}
	}
	return true;
}
public static String substitute(String query, Map<String,String> sublist){
	
	String tstr = get_termstring(query);
	String pred = give_pred(query);
	pred = pred.concat("(");
	List<String> terms = get_terms(tstr);
	for(int i=0;i<terms.size();i++){
		
		String thisterm = terms.get(i);
		if(sublist.containsKey(thisterm)){
			do{
				String val = sublist.get(thisterm);
				if(val!=null){
						thisterm = val;
				}
				if(Character.isUpperCase(thisterm.charAt(0))){
					sublist.remove(thisterm);
				}
			}while(sublist.containsKey(thisterm));
			if(Character.isUpperCase(thisterm.charAt(0))){
				sublist.put(thisterm, thisterm);
			}
			pred = pred.concat(thisterm);
			pred = pred.concat(",");
		}
		else{
			pred = pred.concat(terms.get(i));
			pred = pred.concat(",");
		}
	}
	pred = pred.substring(0,pred.length()-1);
	pred = pred.concat(")");
	return pred;
}


public static Map<String,String> compose(String q, String var, Map<String,String> oldmap){
	
	Map<String,String> newmap = new HashMap<String,String>();
	String tstr = get_termstring(var);
	List<String> terms = get_terms(tstr);
	newmap.putAll(oldmap);
	List<String> oldset = new ArrayList<String>();
	List<String> const_set = new ArrayList<String>();
	String tempstr = get_termstring(q);
	const_set = get_terms(tempstr);
	for(int i=0;i<terms.size();i++){
		String temp = terms.get(i);
		if(Character.isUpperCase(temp.charAt(0))==true){
			
			String test = const_set.get(i);
			if(Character.isUpperCase(test.charAt(0))==false){
				
				newmap.put(test, temp);
			}
			else{
				
				if(test.equals(temp)==false){
					newmap.clear();
					return newmap;
				}
				else{
					
					newmap.put(temp, temp);
				}
			}
		}
		else{
			
			if(oldmap.isEmpty()==false){
				
				if(oldmap.containsKey(temp)==false){
					
					newmap.put(temp, const_set.get(i));
				}
			}
			else{
				
				newmap.put(temp, const_set.get(i));
			}
		}
		
	}
	return newmap;
}

public static List<Map<String,String>> check_part_fact(String query, Map<String,String> sublist){
	
	String pred = give_pred(query);
	String termstr = get_termstring(query);
	List<String> tlist = get_terms(termstr);
	List<Map<String,String>> ret_list = new ArrayList<Map<String,String>>();
	for(Map.Entry<Integer, String> e : facts.entrySet()) {
	    Integer key = e.getKey();
	    String value = e.getValue();
	    String fact_pred = give_pred(value);
	    Map<String, String> matchlist = new HashMap<String,String>();
	    if(fact_pred.equals(pred)){
	    	
			String rhsremstr = get_termstring(value);
			List<String> rhstlist = get_terms(rhsremstr);
	    	int i=0;
			int flag=1;
			while(i < tlist.size() && flag ==1){
				
				flag=0;
				String str1 = tlist.get(i);
				String str2= rhstlist.get(i);
				
				if(Character.isUpperCase(str1.charAt(0))){
					
					 if(str1.equals(str2)){
						
						flag=1;
					 }
				}
				
				else if(Character.isLowerCase(str1.charAt(0))){
					
					if(sublist.containsKey(str1)==false){
						
						matchlist.put(str1,str2);
						flag=1;
					}
					else{
						if(sublist.get(str1).equals(str2)){
							flag=1;
						}
					}
					
				}
				i++;
			}
			if(flag==1){
				
				matchlist.putAll(sublist);
				ret_list.add(matchlist);
			}
	    }
	}
	return ret_list;
}

//Split conjoined clauses and return them in list
	public static List<String> split_conj(String clstr){
		
		List<String> clist = new ArrayList<String>();
		if(clstr.contains("^") == true){
			
			StringTokenizer str = new StringTokenizer(clstr, "^");  
	    	while(str.hasMoreTokens()){
	    		
	    		 clist.add(str.nextToken().trim());
	    	}
		}
		else{
			
			 clist.add(clstr.trim());
		}
		
		return clist;
	}
	
	//Split all terms of a predicate and return them in list
	public static List<String> get_terms(String termstr){
		
		List<String> termlist = new ArrayList<String>();
		if(termstr.contains(",")){
			
			StringTokenizer strnew = new StringTokenizer(termstr, ","); 
			while(strnew.hasMoreTokens()){
				
				termlist.add(strnew.nextToken().trim());
			}
		}
		else{
			
			termlist.add(termstr.trim());
		}
		
		return termlist;
	}
	
	public static String give_pred(String claus){
		
		StringTokenizer str = new StringTokenizer(claus, "(");  
		String pred = str.nextToken().trim();
		return pred;
	}
	
public static String get_termstring(String clause){
		
		StringTokenizer str = new StringTokenizer(clause, "(");  
		String pred = str.nextToken().trim();
		String remstr = str.nextToken().trim();
		String termstr = remstr.substring(0, remstr.length()-1);
		return termstr;
	}

public static void splitclause(String clause, Integer cl_no){
		
	
	//If implication, separate LHS and RHS and store
			if(clause.contains("=>") == true){
				
				StringTokenizer str = new StringTokenizer(clause, "=>");  
		    	String newString = str.nextToken().trim();
		    	lhsclause.put(cl_no, newString);
		    	newString = str.nextToken().trim();  
			    rhsclause.put(cl_no, newString);
			    StringTokenizer strhs = new StringTokenizer(newString, "("); 
	    		String factpred = strhs.nextToken().trim();
				if(rhsoccurs.containsKey(factpred)==false){
					
					rhsoccurs.put(factpred, 0);
				}
			    
			}
			else{
				
				//Store as fact 
				facts.put(cl_no, clause.trim());
				StringTokenizer str = new StringTokenizer(clause, "("); 
	    		String factpred = str.nextToken().trim();
				if(occurs.containsKey(factpred)==false){
					
					occurs.put(factpred, 0);
				}
			}
	}

public static String standardize(String q, int qnum){
	
	String tstr = get_termstring(q);
	List<String> terms = get_terms(tstr);
	String pred = give_pred(q);
	String newclause = null;
	pred = pred.concat("(");
	for(int i=0;i<terms.size();i++){
		
		String temp = terms.get(i);
		String newterm;
		if(Character.isUpperCase(temp.charAt(0))==true){
			
			newterm = temp;
		}
		else{
			
			newterm = terms.get(i).concat(String.valueOf(qnum));
		}
		pred=pred.concat(newterm);
		pred = pred.concat(",");
	}
	pred = pred.substring(0, pred.length()-1);
	pred = pred.concat(")");
	return pred;
	}
	
}