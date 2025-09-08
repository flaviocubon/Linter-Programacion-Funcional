module Lintings where

import AST
import LintTypes


--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables (Var x) = [x]
freeVariables (Lit _) = []
freeVariables (Infix _ x y) = freeVariables x ++ freeVariables y
freeVariables (App x y) = freeVariables x ++ freeVariables y
freeVariables (Lam y x) = [var | var <- xs, var /= y]
    where
        xs = freeVariables x
freeVariables (Case x y (_, _, z)) = freeVariables x ++ freeVariables y ++ freeVariables z
freeVariables (If x y z) = freeVariables x ++ freeVariables y ++ freeVariables z


--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r)


class Operable a b c where
    opFunc :: Op -> (b -> a -> c)

instance Operable Integer Integer Integer where
    opFunc :: Op -> Integer -> Integer -> Integer
    opFunc Add = (+)
    opFunc Sub = (-)
    opFunc Mult = (*)
    opFunc Div = div

instance Operable Integer Integer Bool where
    opFunc :: Op -> Integer -> Integer -> Bool
    opFunc Eq = (==)
    opFunc GTh = (>)
    opFunc LTh = (<)

instance Operable Bool Bool Bool where
    opFunc :: Op -> Bool -> Bool -> Bool
    opFunc Eq = (==)
    opFunc And = (&&)
    opFunc Or = (||)

instance Operable [a] a [a] where
    opFunc :: Op -> a -> [a] -> [a]
    opFunc Cons = (:)

instance Operable [a] [a] [a] where
    opFunc :: Op -> [a] -> [a] -> [a]
    opFunc Append = (++)

instance Operable (b -> a) (a -> b) (b -> b) where
    opFunc :: Op -> ((a -> b) -> (b -> a) -> b -> b)
    opFunc Comp = (.)

casoGeneral :: Linting Expr -> Expr -> (Expr, [LintSugg])

casoGeneral f (Infix op x y) = (Infix op xSug ySug, xs ++ ys)
    where (xSug, xs) = f x; (ySug, ys) = f y

casoGeneral f (App x y) = (App xSug ySug, xs ++ ys)
    where (xSug, xs) = f x; (ySug, ys) = f y
    
casoGeneral f (Lam n x) = (Lam n xSug, xs)
    where (xSug, xs) = f x

casoGeneral f (Case x y (n1, n2, z)) = (Case xSug ySug (n1, n2, zSug), xs ++ ys ++ zs)
    where (xSug, xs) = f x; (ySug, ys) = f y; (zSug, zs) = f z

casoGeneral f (If x y z) = (If xSug ySug zSug, xs ++ ys ++ zs)
    where (xSug, xs) = f x; (ySug, ys) = f y; (zSug, zs) = f z

casoGeneral f x = (x,[])


lintComputeConstant :: Linting Expr
lintComputeConstant (Infix op (Lit (LitInt x)) (Lit (LitInt y)))
                        | op == Eq || op == GTh || op == LTh = (Lit (LitBool (opFunc op x y)), [LintCompCst (Infix op (Lit (LitInt x)) (Lit (LitInt y))) (Lit (LitBool (opFunc op x y)))])
                        | ((op == Div) && (y /= 0)) || (opFunc op x y :: Integer) > 0 = (Lit (LitInt (opFunc op x y)), [LintCompCst (Infix op (Lit (LitInt x)) (Lit (LitInt y))) (Lit (LitInt (opFunc op x y)))])
                        | otherwise = (Infix op (Lit (LitInt x)) (Lit (LitInt y)), [])

lintComputeConstant (Infix op (Lit (LitBool x)) (Lit (LitBool y))) = (Lit (LitBool res), [LintCompCst (Infix op (Lit (LitBool x)) (Lit (LitBool y))) (Lit (LitBool res))])
                        where res = opFunc op x y

lintComputeConstant x = casoGeneral lintComputeConstant x;
--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBool :: Linting Expr
lintRedBool (Infix op x (Lit (LitBool y)))
                | op == Eq && y = (x,[LintBool (Infix Eq x (Lit (LitBool True))) x])
                | op == Eq && not y = (App (Var "not") x,[LintBool (Infix Eq x (Lit (LitBool y))) (App (Var "not") x)])
                | otherwise = (Infix op x (Lit (LitBool y)),[])


lintRedBool (Infix op (Lit (LitBool y)) x)
                | op == Eq && y  = (x,[LintBool (Infix Eq x (Lit (LitBool True))) x])
                | op == Eq && not y = (App (Var "not") x,[LintBool (Infix Eq x (Lit (LitBool y))) (App (Var "not") x)])
                | otherwise = (Infix op x (Lit (LitBool y)),[])

lintRedBool x = casoGeneral lintRedBool x
--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCond :: Linting Expr
lintRedIfCond (If (Lit (LitBool True)) x y) = (xIf, xs ++ ys ++ [LintRedIf (If (Lit (LitBool True)) xIf yIf) xIf])
    where (xIf, xs) = lintRedIfCond x; (yIf, ys) = lintRedIfCond y

lintRedIfCond (If (Lit (LitBool False)) x y) = (yIf, xs ++ ys ++ [LintRedIf (If (Lit (LitBool True)) xIf yIf) yIf])
    where (xIf, xs) = lintRedIfCond x; (yIf, ys) = lintRedIfCond y

lintRedIfCond x = casoGeneral lintRedIfCond x

--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)    
lintRedIfAnd :: Linting Expr
lintRedIfAnd (If x e (Lit (LitBool False))) = (Infix And xIf eIf, xs ++ es ++ [LintRedIf (If x e (Lit (LitBool False))) (Infix And x e)])
    where (xIf, xs) = lintRedIfAnd x; (eIf, es) = lintRedIfAnd e
lintRedIfAnd x = casoGeneral lintRedIfAnd x
--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr (If x (Lit (LitBool True)) e) = (Infix Or xIf eIf,  xs ++ es ++ [LintRedIf (If x (Lit (LitBool True)) e) (Infix Or x e)])
    where (xIf, xs) = lintRedIfOr x; (eIf, es) = lintRedIfOr e

lintRedIfOr x = casoGeneral lintRedIfOr x

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
lintNull (Infix Eq e (Lit LitNil)) = (App (Var "null") eNull, es ++ [LintNull (Infix Eq e (Lit LitNil)) (App (Var "null") eNull)])
    where (eNull, es) = lintNull e

lintNull (Infix Eq (Lit LitNil) e) = (App (Var "null") eNull, es ++ [LintNull (Infix Eq e (Lit LitNil)) (App (Var "null") eNull)])
    where (eNull, es) = lintNull e

lintNull (Infix Eq (App (Var "length") e) (Lit (LitInt 0)) ) = (App (Var "null") eNull, es ++ [LintNull (Infix Eq (App (Var "length") e) (Lit (LitInt 0))) (App (Var "null") eNull)]) -- ESTE
    where (eNull, es) = lintNull e

lintNull (Infix Eq (Lit (LitInt 0)) (App (Var "length") e)) = (App (Var "null") eNull, es ++ [LintNull (Infix Eq (App (Var "length") e) (Lit (LitInt 0))) (App (Var "null") eNull)])
    where (eNull, es) = lintNull e

lintNull x = casoGeneral lintNull x
--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend (Infix Append (Infix Cons e (Lit LitNil)) es) = (Infix Cons e esSug, esS ++ [LintAppend (Infix Append (Infix Cons e (Lit LitNil)) esSug) (Infix Cons e esSug)])
    where (esSug, esS) = lintAppend es

lintAppend x = casoGeneral lintAppend x

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)
 
lintCompAux :: Expr -> Expr
lintCompAux (App x (App y z)) = App (Infix Comp x y) z

lintComp :: Linting Expr
lintComp (App x (App y w)) = (comp, yws ++ [LintComp (App x ywComp) comp])
    where (ywComp, yws) = lintComp (App y w); comp = lintCompAux (App x ywComp)

lintComp x = casoGeneral lintComp x

--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta (Lam n (Var x)) 
    | n /= x = (Var x,[LintEta (Lam x (Var x)) (Var x)])
    | otherwise = (Lam n (Var x),[])

lintEta (Lam y (App e (Var x)))
    | y == x && x `notElem` freeVariables e = (eLam, es ++ [LintEta (Lam y (App eLam (Var x))) eLam])
    | otherwise = (Lam y (App eLam (Var x)), es)
    where
        (eLam, es) = lintEta e
        
lintEta x = casoGeneral lintEta x
--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef

lintMap (FunDef funcN (Lam lN (Case (Var l) (Lit LitNil) (x, xsN, Infix Cons e (App (Var func) (Var xs))))))
    | lN == l && xsN == xs && funcN == func && func `notElem` fv && xs `notElem` fv && l `notElem` fv = (FunDef func (App (Var "map") (Lam x e)), 
    [LintMap (FunDef funcN (Lam lN (Case (Var l) (Lit LitNil) (x, xsN, Infix Cons e (App (Var func) (Var xs)))))) (FunDef func (App (Var "map") (Lam x e)))])
    | otherwise = (FunDef funcN (Lam lN (Case (Var l) (Lit LitNil) (x, xsN, Infix Cons e (App (Var func) (Var xs))))),[])
        where fv = freeVariables e;

lintMap x = (x,[])

--------------------------------------------------------------------------------
-- Combinación de Lintings
--------------------------------------------------------------------------------


-- Dada una transformación a nivel de expresión, se construye
-- una transformación a nivel de función
liftToFunc :: Linting Expr -> Linting FunDef
liftToFunc l (FunDef n x) = (FunDef n xL, xs)
    where (xL, xs) = l x

-- encadenar transformaciones:
(>==>) :: Linting a -> Linting a -> Linting a
(lint1 >==> lint2) x = (xSug2,xs1 ++ xs2)
    where (xSug1, xs1) = lint1 x; (xSug2, xs2) = lint2 xSug1 

-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Linting a -> Linting a
lintRec lints ini
    | null zs = (xSug, xs)
    | otherwise = (zSug, xs ++ zs)
    where
        (xSug, xs) = lints ini; (zSug, zs) = lints xSug