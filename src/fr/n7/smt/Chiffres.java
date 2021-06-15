/* Manal Hajji - Younes Saoudi*/
package fr.n7.smt;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import com.microsoft.z3.*;

/**
 * Classe qui implémente l'algorithme de BMC pour la partie "chiffres"
 * du jeu "des chiffres et des lettres".
 */
public class Chiffres {

    /**
     * Contexte utilisé par l'instance Chiffres pour créer les formules,
     * solveurs, etc.
     */
    private Context context;

    /** Cache de constantes booléennes, indicé par leur nom. */
    private HashMap<String, BoolExpr> boolCache = new HashMap<>();

    /** Cache de constantes booléennes, indicé par leur nom. */
    private HashMap<String, BitVecExpr> bvCache = new HashMap<>();

    /** Cache de constantes booléennes, indicé par leur nom. */
    private HashMap<String, IntExpr> intCache = new HashMap<>();

    /** Cache de constantes booléennes, indicé par leur nom. */
    private HashMap<String, ArrayExpr> arrayCache = new HashMap<>();

    /** Nombre de bits de la représentation des bitvectors. */
    private int bvBits;

    /** Sorte bitvector de taille bvBits. */
    private Sort bvSort;

    /**
     * Sorte tableaux à indices intSort et elements bitvectors de
     * taille bvBits.
     */
    private Sort bvArraySort;

    /** Sorte des entiers mathématiques. */
    private Sort intSort;

    /** Constantes numériques pour le calcul du système de transition. */
    private int[] nums;

    /** Valeur cible du calcul du système de transition. */
    private int target;

    /** Nombre maximum d'étapes de calcul du système de transition. */
    private int maxNofSteps;

    /** Si vrai alors interdiction d'overflow sur les operations bitvector. */
    private boolean noOverflows;
    private BigInteger maxBvRange;
    private BigInteger minBvRange;

    /**
     * Initialise tous les attributs de la classe: paramètres utilisateur,
     * contexte, sortes.
     */
    public Chiffres(int[] _nums, int _target, int _bvBits, boolean _noOverflows) {
        nums        = _nums;
        target      = _target;
        bvBits      = _bvBits;
        maxBvRange  = new BigInteger("2").pow(bvBits-1).subtract(new BigInteger("1"));
        minBvRange  = new BigInteger("2").pow(bvBits-1).negate();
        maxNofSteps = 2 * nums.length - 1;
        noOverflows = _noOverflows;

        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("model", "true");
        cfg.put("proof", "true");

        context     = new Context(cfg);
        intSort     = context.mkIntSort();
        bvSort      = context.mkBitVecSort(bvBits);
        bvArraySort = context.mkArraySort(intSort, bvSort);
        boolCache   = new HashMap<>();
        bvCache     = new HashMap<>();
        intCache    = new HashMap<>();
        arrayCache  = new HashMap<>();
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private BoolExpr boolConst(String name) {
        BoolExpr res = boolCache.get(name);

        if (res == null) {
            res = context.mkBoolConst(name);
            boolCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private BitVecExpr bvConst(String name) {
        BitVecExpr res = bvCache.get(name);

        if (res == null) {
            res = context.mkBVConst(name, bvBits);
            bvCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private IntExpr intConst(String name) {
        IntExpr res = intCache.get(name);

        if (res == null) {
            res = context.mkIntConst(name);
            intCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private ArrayExpr arrayConst(String name) {
        ArrayExpr res = arrayCache.get(name);

        if (res == null) {
            res = context.mkArrayConst(name, intSort, bvSort);
            arrayCache.put(name, res);
        }

        return res;
    }

    /** Expression vraie ssi exactement une des exprs est vraie. */
    private BoolExpr exactlyOne(BoolExpr... exprs) {
        return context.mkAnd(context.mkOr(exprs), atMostOne(exprs));
    }

    /** Expression vraie ssi au plus une des exprs est vraie. */
    private BoolExpr atMostOne(BoolExpr... exprs) {
        ArrayList<BoolExpr> conjuncts = new ArrayList<>();

        for (BoolExpr expr : exprs) {
            ArrayList<BoolExpr> otherExprs = new ArrayList<>();
            for (BoolExpr e : exprs) {
                if (e != expr) {
                    otherExprs.add(e);
                }
            }

            BoolExpr bigOr = context.mkOr(otherExprs.stream().toArray(BoolExpr[]::new));
            BoolExpr res = context.mkImplies(expr, context.mkNot(bigOr));

            conjuncts.add(res);
        }

        return context.mkAnd(conjuncts.stream().toArray(BoolExpr[]::new));
    }

    /** Convertit un int java en valeur symbolique bitvector Z3. */
    private BitVecNum toBvNum(int num) {
        if (noOverflows) {
            BigInteger bigNum = new BigInteger(String.valueOf(num));

            if (bigNum.compareTo(minBvRange) >= 0 && bigNum.compareTo(maxBvRange) <= 0)
                return context.mkBV(num, bvBits);
            else
                throw new Error("le numeral " + String.valueOf(num) +
                                " dépasse la capacité des bitvectors signés de taille " +
                                String.valueOf(bvBits));
        } else {
            return context.mkBV(num, bvBits);
        }
    }

    /**
     * Trigger de l'action "pousser un numéral sur la pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr pushNumVar(int step, int num) {
        return boolConst("push_" + String.valueOf(num) + "@" +
                         String.valueOf(step));
    }

    /**
     * Trigger de l'action "additionner les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr addVar(int step) {
        return boolConst("add@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "soustraire les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr subVar(int step) {
        return boolConst("sub@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "multiplier les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr mulVar(int step) {
        return boolConst("mul@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "diviser les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr divVar(int step) {
        return boolConst("div@" + String.valueOf(step));
    }

    /** Variable d'état représentant la pile au pas d'exécution "step". */
    private ArrayExpr stackStateVar(int step) {
        return arrayConst("stack@" + String.valueOf(step));
    }

    /**
     * Variable d'état représentant l'indice de dessus de pile au pas
     * d'exécution "step".
     */
    private IntExpr idxStateVar(int step) {
        return intConst("idx@" + String.valueOf(step));
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "push(num)".
     */
    private BoolExpr pushNumFormula(int step, int num) {
    	/*
        System.out.println("Attention : la méthode pushNumFormula n'est pas définie !");
        */
    	/*Instantion des états représentant la pile et son indice de dessus au pas step et step+1 */
    	ArrayExpr stackState = stackStateVar(step);
    	IntExpr idxState = idxStateVar(step);
    	ArrayExpr nextStackState = stackStateVar(step+1);
    	IntExpr nextIdxState = idxStateVar(step+1);
    	ArithExpr a1 = context.mkSub(idxState,context.mkInt(1));
    	ArithExpr a2 = context.mkSub(nextIdxState,context.mkInt(1));
    	// retourne un boolExpr true si le num n'est jamais ajouté.
    	BoolExpr neverUsed = context.mkTrue();
     
    	if (step > 0){
 
    		for (int i = 0; i <step; i++){
    			BoolExpr isPushed = pushNumVar(i,num);
    			neverUsed = context.mkAnd(neverUsed, context.mkNot(isPushed));
    		}
    	}
    	
    	BoolExpr idxOk = context.mkEq(a2, context.mkAdd(a1,context.mkInt(1)));
        BoolExpr stackOk = context.mkEq(nextStackState, context.mkStore(stackState,a2,toBvNum(num)));
 
        return context.mkAnd(idxOk, stackOk, neverUsed);
    }


    private interface ActionVar {
        /**
         * Retourne la variable trigger de l'action au step donné.
         */
        BoolExpr get(int step);
    }

    private interface ActionResult {
        /**
         * Retourne l'expression du résultat de l'action au step donné
         * en fonction de e1 et e2, les deux valeurs du dessus de la pile.
         */
        BitVecExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }

    private interface ActionPrecondition {
        /**
         * Retourne l'expression de la précondition de l'action au step
         * donné en fonction de e1 et e2, les deux valeurs du dessus de
         * la pile.
         */
        BoolExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }


    private BoolExpr actionFormula(int step, ActionVar actVar, ActionPrecondition precond, ActionResult opRes) {
        //System.out.println("Attention : la méthode actionFormula n'est pas définie !");
    	/*Instantion des états représentant la pile et son indice de dessus au pas step et step+1 */
    	ArrayExpr stackState = stackStateVar(step);
    	IntExpr idxState = idxStateVar(step);
    	ArrayExpr nextStackState = stackStateVar(step+1);
    	IntExpr nextIdxState = idxStateVar(step+1);
    	
    	ArithExpr a1 = context.mkSub(idxState,context.mkInt(1));
    	ArithExpr a2 = context.mkSub(nextIdxState,context.mkInt(1));
    	
    	// L’action à effectuer est encapsulée dans un objet de typeActionVar
    	BoolExpr actionVar = actVar.get(step);
    	
 
    	BitVecExpr vec1 =(BitVecExpr) context.mkSelect(stackState, a1);
    	BitVecExpr vec2 =(BitVecExpr) context.mkSelect(stackState, a2);
 
    	BoolExpr precBool = precond.get(step, vec1, vec2); 
 
    	BoolExpr Cond = context.mkEq(opRes.get(step, vec1, vec2),context.mkSelect(nextStackState, a2));
    	BoolExpr idxOk = context.mkEq(context.mkAdd(a2, context.mkInt(1)), a1);
    	ArrayExpr store = context.mkStore(stackState, a2, context.mkSelect(nextStackState, a2));
    	BoolExpr stackOk = context.mkEq(nextStackState, context.mkStore(store, a1, context.mkBV(0, bvBits)));
    	
    	return context.mkAnd(actionVar, precBool, Cond, idxOk, stackOk);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "addition".
     */
    private BoolExpr addFormula(int step) {
       // System.out.println("Attention : la méthode addFormula n'est pas définie !");
    	ActionVar actionVar = this::addVar;
    	
        ActionPrecondition actionPrecondition = (s, vec1, vec2) -> {
        	
				ArithExpr a = context.mkSub(idxStateVar(s), context.mkInt(1));
				BoolExpr noOverf = context.mkTrue();
				if (noOverflows) {
					noOverf = context.mkBVAddNoOverflow(vec1, vec2, false);
				}
				return context.mkAnd(noOverf,context.mkGe(a, context.mkInt(1)));			
        	
        };
        
        ActionResult actionResult =  (s, vec1, vec2) -> {
        	
				return context.mkBVAdd(vec1, vec2);
		};
		
        return actionFormula(step, actionVar, actionPrecondition, actionResult);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "soustraction".
     */
    private BoolExpr subFormula(int step) {
        //System.out.println("Attention : la méthode subFormula n'est pas définie !");
    	ActionVar actionVar = this::subVar;
        ActionPrecondition actionPrecondition = (s, vec1, vec2) -> {
        
        		
				ArithExpr a = context.mkSub(idxStateVar(s), context.mkInt(1));
				BoolExpr notNegative = context.mkTrue();
				if (noOverflows) {
					notNegative = context.mkBVUGE(vec1, vec2);
				}
				return context.mkAnd(notNegative,context.mkGe(a, context.mkInt(1)));			
        	
        };
        ActionResult actionResult = (s, vec1, vec2) -> {

				return context.mkBVSub(vec1, vec2);
        };
        
        return actionFormula(step, actionVar, actionPrecondition, actionResult);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "multiplication".
     */
    private BoolExpr mulFormula(int step) {
        //System.out.println("Attention : la méthode mulFormula n'est pas définie !");
    	ActionVar actionVar = this::mulVar;
    	
        ActionPrecondition actionPrecondition = (s, vec1, vec2) -> {
        	
				ArithExpr a = context.mkSub(idxStateVar(step), context.mkInt(1));
				BoolExpr noOverf = context.mkTrue();
				if (noOverflows) {
					noOverf = context.mkBVUGE(vec1, vec2);
				}
				return context.mkAnd(noOverf,context.mkGe(a, context.mkInt(1)));			
        	
        };
        
        ActionResult actionResult = (s, vec1, vec2) -> {

				return context.mkBVMul(vec1, vec2);
			
        };
        
        return actionFormula(step, actionVar, actionPrecondition, actionResult);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "division".
     */
    private BoolExpr divFormula(int step) {
        //System.out.println("Attention : la méthode divFormula n'est pas définie !");
    	ActionVar actionVar = this::divVar;
    	
        ActionPrecondition actionPrecondition = (s, vec1, vec2) -> {
        		
				ArithExpr a = context.mkSub(idxStateVar(s), context.mkInt(1));
				return context.mkAnd(context.mkGe(a, context.mkInt(1)), context.mkNot(context.mkEq(context.mkBV(0, bvBits), vec2)));
        	
        };
        
        ActionResult actionResult = (s, vec1, vec2) -> {

				return context.mkBVUDiv(vec1, vec2);
				
        };
        
        return actionFormula(step, actionVar, actionPrecondition, actionResult);
        
    }

    /**
     * Tableau contenant tous les triggers d'actions push, mul,
     * div, add, sub au pas "step".
     */
    private BoolExpr[] allActions(int step) {
        ArrayList<BoolExpr> arr = new ArrayList<>();

        for (int num : nums) {
            arr.add(pushNumVar(step, num));
        }

        arr.add(mulVar(step));
        arr.add(divVar(step));
        arr.add(addVar(step));
        arr.add(subVar(step));

        return arr.stream().toArray(BoolExpr[]::new);
    }

    /**
     * Formule vraie ssi les états aux pas step et step+1 sont liés par
     * une transition d'action.
     */
    private BoolExpr transitionFormula(int step) {
        //System.out.println("Attention : la méthode transitionFormula n'est pas définie !");
    	BoolExpr actions[] = allActions(step);
    	BoolExpr onlyOne = exactlyOne(actions);
    	ArrayList<BoolExpr> trigger = new ArrayList<>();
 
    	for(int n: nums) {
    		BoolExpr isPushed = pushNumVar(step, n);
    		BoolExpr isTransitionOk = pushNumFormula(step, n);
    		trigger.add(context.mkImplies(isPushed, isTransitionOk));
    	}
    	
    	BoolExpr[] varList = {addVar(step), subVar(step), mulVar(step), divVar(step)}; 
		BoolExpr[] formulaList = {addFormula(step), subFormula(step), mulFormula(step), divFormula(step)};
    	
		for(int i=0; i<varList.length; i++) {
			trigger.add(context.mkImplies(varList[i], formulaList[i]));
		}
    	
    	BoolExpr result = context.mkAnd(trigger.stream().toArray(BoolExpr[]::new));
    	
    	return context.mkAnd(onlyOne, result);

    }

    /**
     * Formule vraie ssi la pile est dans son état initial (au pas 0,
     * toutes les cellules à zéro et dessus de pile à zero).
     */
    private BoolExpr initialStateFormula() {
        // System.out.println("Attention : la méthode initialStateFormula n'est pas définie !");
    	ArrayExpr stackState = stackStateVar(0);
    	IntExpr idxState = idxStateVar(0);
    	BoolExpr result =  context.mkEq(idxState, context.mkInt(0));
    	
    	for(int i=0 ; i < maxNofSteps; i++)
    	{
    		BitVecExpr element = (BitVecExpr) context.mkSelect(stackState,context.mkInt(i));
    		result = context.mkAnd(result, context.mkEq(element, context.mkBV(0,  bvBits)));
    	}
    	
    	return result; 
    }

    /**
     * Formule vraie ssi la pile ne contient qu'un élément qui est égal
     * à la valeur cible au pas "step".
     */
    private BoolExpr finalStateFormula(int step) {
        //System.out.println("Attention : la méthode finalStateFormula n'est pas définie !");
    	ArrayExpr stackState = stackStateVar(step);
    	IntExpr idxState = idxStateVar(step);
    	ArithExpr a = context.mkSub(idxState, context.mkInt(1));
    	
    	BoolExpr idxOk = context.mkEq(a, context.mkInt(0));
    	BoolExpr valOk = context.mkEq(context.mkSelect(stackState, a), context.mkBV(target, bvBits));
    	
    	return context.mkAnd(idxOk, valOk);
    }

    /**
     * Algorithme de résolution exacte. Déroule une boucle de
     * model-checking borné de la relation de transition depuis l'état
     * initial sur au plus maxNofSteps. Pour chaque itération de
     * model-checking, on ajoute une formule de transition pour le step
     * suivant dans le solveur, on pousse la formule d'état final, on
     * lance une résolution. Si le problème est SAT, on imprime la
     * solution, si le problème est UNSAT, on retire la formule d'état
     * final et on passe à l'itération suivante. Si le problème est
     * UNKNOWN, on retourne le status UNKOWN. Si le problème est UNSAT
     * pour toutes les itérations, on retourne le status UNSAT.
     */
    private Status solveExact(int timeout) {
 
    	Status status = Status.UNSATISFIABLE;
        Solver solver = context.mkSolver();
        solver.add(initialStateFormula());
        
        
		for (int i = 0; i < maxNofSteps; i++) {
			solver.add(transitionFormula(i));
			solver.push();
			solver.add(finalStateFormula(i + 1));
			status = solver.check();
			System.out.println(status + " : " + (i+1));
			if (status == Status.SATISFIABLE) {
				printModel(solver.getModel(), i);
				break;
			} else {
				solver.pop();
			}
		}
 
        if (timeout > 0) {
        	Params p = context.mkParams();
            p.add("timeout", timeout);
            solver.setParameters(p);
            System.out.println("\n\nsolveExact with timeout " + String.valueOf(timeout));
        } else {
            System.out.println("\n\n solveExact without timeout" );
        }
        
        return status;
    }

    /**
     * Formule vraie ssi la pile n'est pas dans son état final au pas
     * "step".
     */
    private BoolExpr finalStateApproxFormula(int step) {
        //System.out.println("Attention : la méthode finalStateApproxFormula n'est pas définie !");  	
        return context.mkNot(finalStateFormula(step));
    }

    /**
     * Critère d'optimisation, écart en valeur absolue entre la valeur
     * du dessus de la pile et la valeur cible au pas "step".
     */
    private BitVecExpr finalStateApproxCriterion(int step) {
        //System.out.println("Attention : la méthode finalStateApproxCriterion n'est pas définie !");
        ArrayExpr state = stackStateVar(step);
        IntExpr idxState = idxStateVar(step);
        ArithExpr a = context.mkSub(idxState, context.mkInt(1));
       
        BitVecExpr vec = context.mkBVSub((BitVecExpr) context.mkSelect(state, a), context.mkBV(target, bvBits));
        
        return (BitVecExpr) context.mkITE(context.mkBVSGE(vec, context.mkBV(0, bvBits)), vec, context.mkBVNeg(vec));
    }

    /**
     * Algorithme de résolution approchée par optimisation max-SMT. À
     * chaque étape de BMC, on minimise la distance à la cible. Le
     * solveur d'optimisation n'est pas incrémental donc push et pop ne
     * sont pas disponibles, on instancie donc un nouveau solveur et
     * toutes les contraintes jusqu'au pas "step" à chaque itération,
     * ainsi que le critère à optimiser. Pour chaque itération le
     * problème est sensé être SAT et on imprime la solution à chaque
     * itération. Si le problème est UNSAT, on retire la formule d'état
     * final et on passe à l'itération suivante. Si le problème est
     * UNKNOWN, on retourne le status UNKOWN. Si le problème était SAT
     * pour toutes les itérations, on retourne le status SAT.
     */
    private Status solveApprox(int timeout) {
        //System.out.println("Attention : la méthode solveApprox n'est pas définie !");

        // ce solver n'est pas incrémental, il faut le recréer à
        // chaque nouvelle itération du BMC.
        // utiliser les méthodes suivantes sur le solveur (attention
        // aux majuscules !) :
        // - Add pour ajouter une formule
        // - MkMinimize pour ajouter un critère à optimiser
        // - Check pour résoudre
        
        Status status = Status.UNSATISFIABLE;
        
        for(int i=0; i< maxNofSteps; i++) {
        	Optimize solver = context.mkOptimize();
        	solver.Add(initialStateFormula());
        	for(int j=0; j<= i ; j++) {
        		solver.Add(transitionFormula(j));
        	}
        	solver.Add(finalStateApproxFormula(i+1));
        	solver.MkMinimize(finalStateApproxCriterion(i + 1));
			status = solver.Check();
			System.out.println(status + " : " + (i+1));
			if (status == Status.SATISFIABLE) {
				printModel(solver.getModel(), i);
				System.out.println();
			}
			
			if (timeout > 0) {
				Params p = context.mkParams();
				p.add("timeout", timeout);
				solver.setParameters(p);
			}
		}

		return status;
	}
        	

    /**
     * Résout le problème en essayant une résolution exacte,
     * puis une résolution approximative en cas d'échec.
     */
    Status solve(int timeout) {
        printParams();

        Status s = solveExact(timeout);

        if (s != Status.SATISFIABLE) {
            s = solveApprox(timeout);
        }

        return s;
    }

    /** Affiche le contenu de la pile en ASCII sur sdtout. */
    private void printStackAtStep(Model m, int step) {
        for (int idx = 0; idx <= maxNofSteps; idx++) {
            BitVecExpr resbv =
                (BitVecExpr) context.mkSelect(stackStateVar(step),
                                              context.mkInt(idx));
            IntExpr resi = context.mkBV2Int(resbv, true);

            if (m.eval(context.mkEq(idxStateVar(step),
                                    context.mkInt(idx)), true).isTrue()) {
                System.out.print(" <| ");
            } else {
                System.out.print(" | ");
            }

            System.out.print(m.eval(resi, true));
        }

        System.out.println();
    }

    /**
     * Affiche le contenu d'un modèle m obtenu par BMC jusqu'à
     * la profondeur steps.
     */
    private void printModel(Model m, int steps) {
        System.out.print("init ~> ");
        printStackAtStep(m, 0);

        for (int step = 0; step <= steps; step++) {
            for (int num : nums) {
                if (m.eval(pushNumVar(step, num), true).isTrue()) {
                    System.out.print("push " + String.valueOf(num) + " ~> ");
                }
            }

            if (m.eval(mulVar(step), true).isTrue()) {
                System.out.print("mul ~> ");
            }

            if (m.eval(divVar(step), true).isTrue()) {
                System.out.print("div ~> ");
            }

            if (m.eval(addVar(step), true).isTrue()) {
                System.out.print("add ~> ");
            }

            if (m.eval(subVar(step), true).isTrue()) {
                System.out.print("sub ~> ");
            }

            printStackAtStep(m, step + 1);
        }
    }

    private void printParams() {
        System.out.println("\nParameters:");
        System.out.println("- bvBits     :" + String.valueOf(bvBits));
        System.out.println("- noOverflows:" + String.valueOf(noOverflows));
        System.out.println("- nums       :" + Arrays.toString(nums));
        System.out.println("- target     :" + String.valueOf(target));
    }
}
