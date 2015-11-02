import java.util.HashMap;
import java.util.Iterator;
import java.util.Set;

// Based on a B specification from Marie-Laure Potet.

public class Explosives{
    public int nb_inc = 0;
    public String [][] incomp = new String[50][2];
    public int nb_assign = 0;
    public String [][] assign = new String[30][2];
 
 	/** Le nombre de rêgles d'incompatibilité doit être compris entre 0 et 49 pour ne pas dépasser du tableau */
    /*@ public invariant // Prop 1
      @ (0 <= nb_inc && nb_inc < 50);
      @*/
      
    /** Le nombre d'assignement doit être compris entre 0 et 29 pour ne pas dépasser du tableau */
    /*@ public invariant // Prop 2
      @ (0 <= nb_assign && nb_assign < 30);
      @*/
      
    /** Chaque icompatibilité doit être entre deux produits. (c'est celui qui est en 0 qui est incompatible avec celui qui est en 1) */
    /*@ public invariant // Prop 3
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @         incomp[i][0].startsWith("Prod") && incomp[i][1].startsWith("Prod"));
      @*/
      
    /** Chaque assignement doit être entre un batiment et un produit (d'abord le batiment puis le produit) */
    /*@ public invariant // Prop 4
      @ (\forall int i; 0 <= i && i < nb_assign; 
      @         assign[i][0].startsWith("Bat") && assign[i][1].startsWith("Prod"));
      @*/
      
    /** Un porduit ne peut pas être incompatible avec lui-même */
    /*@ public invariant // Prop 5
      @ (\forall int i; 0 <= i && i < nb_inc; !(incomp[i][0]).equals(incomp[i][1]));
      @*/
      
    /** La relation d'incompatibilité est réflexive. */
    /*@ public invariant // Prop 6
      @ (\forall int i; 0 <= i && i < nb_inc; 
      @        (\exists int j; 0 <= j && j < nb_inc; 
      @           (incomp[i][0]).equals(incomp[j][1]) 
      @              && (incomp[j][0]).equals(incomp[i][1]))); 
      @*/

    /** Deux produits incompatibles ne peuvent être placés dans un même bâtiment. */
    /*@ public invariant // Prop 7
      @ (\forall int i; 0 <= i &&  i < nb_assign; 
      @     (\forall int j; 0 <= j && j < nb_assign; 
      @        (i != j && (assign[i][0]).equals(assign [j][0])) ==>
      @        (\forall int k; 0 <= k && k < nb_inc;
      @           (!(assign[i][1]).equals(incomp[k][0])) 
      @              || (!(assign[j][1]).equals(incomp[k][1])))));
      @*/

    /** Précondition : prod1 et prod2 doivent être différents */
    /** Précondition : prod1 et prod2 sont 2 produits */
    //@requires nb_inc >= 0;
    //@requires nb_inc < 48;
    //@requires !(prod1.equals(prod2));
    //@requires prod1.startsWith("Prod") && prod2.startsWith("Prod");
    /** Précondition : Deux produits déclarés incompatibles ne peuvent pas avoir été placés dans un même bâtiment auparavant */
    /*@requires 
      @	(\forall int i; 0 <= i && i < nb_assign;
      @		(\forall int j; 0 <= j && j < nb_assign;
      @			(i != j && (assign[i][0]).equals(assign[j][0])) && (!(assign[i][1].equals(assign[j][1]))) ==>
      @				(!((assign[i][1].equals(prod1) || assign[i][1].equals(prod2)) &&
      @				   (assign[j][1].equals(prod1) || assign[j][1].equals(prod2))))));
     */
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
    
    
	/*@ensures \result != null <==>
		@ (\forall int i; 0 <= i && i < nb_assign;
		@	(!assign[i][0].equals(\result)) || compatible(assign[i][1], prod));
		@
	*/
    /** Si le produit est déjà stocké dans un bâtiment, on renvoie ce bâtiment
     * Sinon, on renvoie le premier bâtiment où le produit peut être stocké
     * Si le produit ne peut être stocké dans aucun bâtiment, on renvoie null
     */
    public String findBat(String prod){
    	for(int i = 0; i < nb_assign; i++){
		if(assign[i][1].equals(prod)){
			return assign[i][0];
		}
	}
    	
    	for(int i = 0; i < nb_assign; i++){
    		String b = null;
    		boolean incomp = false;
    		if(compatible(assign[i][1], prod)){
    			b = assign[i][0]; 
    			for(int j = 0; j < nb_assign; j++){
    				if(assign[j][0].equals(b)){
    					if(compatible(assign[j][1], prod) == false){
    						incomp = true;
    						break;
    					}
    				}
    			}
    			if(incomp == false){
    				return b;
    			}
    		}
    	}
    	return null;
    }
    
    //@requires prod1.startsWith("Prod");
    //@requires prod2.startsWith("Prod");
    /*@ensures \result == true ==>
    	@	(\forall int i; 0 <= i && i < nb_inc;
    	@		((!incomp[i][0].equals(prod1)) || (!incomp[i][1].equals(prod2))));
    	@*/
    public boolean compatible(String prod1, String prod2){
    	for(int i = 0; i < nb_inc; i++){
    		if(incomp[i][0].equals(prod1) && incomp[i][1].equals(prod2)){
    			return false;
    		}
    	}
    	return true;
    }
    
    /**
     * Retrouve le bâtiment qui contient prod.
     * Renvoie null si prod n'est pas stocké dans un bâtiment connu.
	* Grâce à la puissance de JML qui ne gère pas les chaînes null, la fonction renvoie en fait une chaîne vide.
     */
    public /*@ pure helper @*/ String contains(String prod){
    	for(int i = 0; i < nb_assign; i++){
    		if(assign[i][1].equals(prod)){
    			return assign[i][0];
    		}
    	}
    	return null;
    }
    
    public void skip(){
    }
}
