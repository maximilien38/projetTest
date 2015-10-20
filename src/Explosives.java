import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

// Based on a B specification from Marie-Laure Potet.

public class Explosives{
    public int nb_inc = 0;
    public String [][] incomp = new String[50][2];
    public int nb_assign = 0;
    public String [][] assign = new String[30][2];
 
 	//le nombre de rêgle d'incompatibilité doit être comprit entre 0 et 49 pour ne pas dépasser du tableau
    /*@ public invariant // Prop 1
      @ (0 <= nb_inc && nb_inc < 50);
      @*/
      
    //le nombre d'assignement doit être comprit entre 0 et 29 pour ne pas dépasser du tableau
    /*@ public invariant // Prop 2
      @ (0 <= nb_assign && nb_assign < 30);
      @*/
      
    //Chaques icompatibilité doit bien être entre deux produits. (c'est celui qui est en 0 qui est incompatible avec celui qui est en 1)
    /*@ public invariant // Prop 3
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @         incomp[i][0].startsWith("Prod") && incomp[i][1].startsWith("Prod"));
      @*/
      
    //chaques assignement doit être entre un batiment et un produit (d'abord le batiment puis le produit)
    /*@ public invariant // Prop 4
      @ (\forall int i; 0 <= i && i < nb_assign; 
      @         assign[i][0].startsWith("Bat") && assign[i][1].startsWith("Prod"));
      @*/
      
    //Un porduit ne peut pas être incompatible avec lui même
    /*@ public invariant // Prop 5
      @ (\forall int i; 0 <= i && i < nb_inc; !(incomp[i][0]).equals(incomp[i][1]));
      @*/
      
    //Si un produit est incompatible avec un autre, il doit figurer dans le tableau dans les deux sens.
    /*@ public invariant // Prop 6
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @        (\exists int j; 0 <= j && j < nb_inc; 
      @           (incomp[i][0]).equals(incomp[j][1]) 
      @              && (incomp[j][0]).equals(incomp[i][1]))); 
      @*/
      
    //Si deux produits sont dans le même batiment il ne faut pas qu'ils soit dans le tableau des incompatibles
    /*@ public invariant // Prop 7
      @ (\forall int i; 0 <= i &&  i < nb_assign; 
      @     (\forall int j; 0 <= j && j < nb_assign; 
      @        (i != j && (assign[i][0]).equals(assign [j][0])) ==>
      @        (\forall int k; 0 <= k && k < nb_inc;
      @           (!(assign[i][1]).equals(incomp[k][0])) 
      @              || (!(assign[j][1]).equals(incomp[k][1])))));
      @*/


    public void add_incomp(String prod1, String prod2){
		incomp[nb_inc][0] = prod1;
		incomp[nb_inc][1] = prod2;
		incomp[nb_inc+1][1] = prod1;
		incomp[nb_inc+1][0] = prod2;
		nb_inc = nb_inc+2;
    }
    
    
    
    //@requires bat.startsWith("Bat");
    //@requires prod.startsWith("Prod");
    //@requires nb_assign < 29;
    //@requires nb_assign >= 0;
    /*@ requires
      @ (\forall int i; 0 <= i &&  i < nb_assign; 
      @        (bat.equals(assign [i][0])) ==> 
      @ 		(\forall int k; 0 <= k && k < nb_inc;
      @           (!prod.equals(incomp[k][0])) || !(assign[i][1]).equals(incomp[k][1])));
      @*/
    public void add_assign(String bat, String prod){
		assign[nb_assign][0] = bat;
		assign[nb_assign][1] = prod;
		nb_assign = nb_assign+1;
    }
    
    
    //@requires prod.startsWith("Prod");
    //@ ensures \old(contains(prod)) ==> \result == null;
	//@ ensures \old(!contains(prod))==> \result.startsWith("Bat");
    /*@ensures  \result != null ==>
    @  				(\forall int i; 0 <= i && i < nb_assign; 
    @					((assign[i][0].equals(\result) ==> compatible(prod,assign[i][1]) )));
    @*/
    public String findBat(String prod)
    {
    	Boolean find = false;
    	String batReturn = null;
    	HashMap<String,Boolean> listBatPossible= new HashMap<String,Boolean>();
    	for( int i = 0; i < nb_assign; i++)
    	{
    		Boolean b = listBatPossible.get(assign[i][0]);
    		if(b == null)
    		{
    			listBatPossible.put(assign[i][0],compatible(assign[i][1],prod));
    		}
    		else
    		{
    			b = listBatPossible.get(assign[i][0]);
    			if(b)
    				listBatPossible.put(assign[i][0],compatible(assign[i][1],prod));   			
    		}
    	}
    	
    	Set<String> keys = listBatPossible.keySet();
    	Iterator<String> it = keys.iterator();
    	while( it.hasNext() && !find)
    	{
    		batReturn = it.next();
    		find = listBatPossible.get(batReturn);
    	}
    	if(find)
    		return batReturn;
    	else
    		return "Bat";
    }
    
    public boolean compatible(String prod1, String prod2)
    {
    	int i = 0;
    	boolean find = false;
    	while(i < nb_inc && !find)
    	{
    		if(incomp[i][0].equals(prod1) && incomp[i][1].equals(prod2))
    			find = true;
    		i++;
    	}
    	return find;
    }
    
    public boolean contains(String prod)
    {
    	int i = 0;
    	while(i < nb_inc && assign[i][1].equals(prod) ){i++;}
    	return i == nb_inc;
    }
    
    public void skip(){
    }
}
