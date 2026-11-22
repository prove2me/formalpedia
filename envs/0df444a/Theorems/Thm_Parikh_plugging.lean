-- Prove2me | Theorems.Thm_Parikh_plugging
-- name    : Parikh.plugging
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:07.197258+00:00
-- url     : https://prove2.me/theorems/eaa60773-2792-4fd8-9845-976b03078ba9
-- title:
--   Parikh: plugging
-- statement:
--   Plugging preserves validity/root and adds weight/size/support (`lem:plug`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L62-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Decomposition.lean#L62-L81

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Definitions.Def_LeanPool_Parikh_TreePlugging
public import Definitions.Def_LeanPool_Parikh_TreeReplacement
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Decomposition
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*}

theorem Parikh.plugging [DecidableEq T] (g : ContextFreeGrammar T) (E t : ParseTree T g.NT)
    (A : g.NT) (hE : OneHole g E A) (ht : Complete g t)
    (hroot : t.root = .nonterminal A) :
    Complete g (E.plug t) ∧ (E.plug t).root = E.root ∧
      (E.plug t).weight = E.weight + t.weight ∧
      (E.plug t).productionSize = E.productionSize + t.productionSize ∧
      (E.plug t).support = E.support ∪ t.support := by sorry
