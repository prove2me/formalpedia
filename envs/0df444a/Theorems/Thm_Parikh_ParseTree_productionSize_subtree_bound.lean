-- Prove2me | Theorems.Thm_Parikh_ParseTree_productionSize_subtree_bound
-- name    : Parikh.ParseTree.productionSize_subtree_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:58.326609+00:00
-- url     : https://prove2.me/theorems/a038467e-22db-4d50-af38-6e5dd58ea458
-- title:
--   Parse Tree: production Size subtree bound
-- statement:
--   A proper subtree has strictly fewer production nodes than its parent tree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L82-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean#L82-L102

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_BoundedCutSupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T N : Type*}
open Parikh.ParseTree

theorem Parikh.ParseTree.productionSize_subtree_bound (t : ParseTree T N) (q : List ℕ)
    (u : ParseTree T N) (hpos : t.subtree q = some u) :
    u.productionSize ≤ t.productionSize ∧
      (q ≠ [] → u.productionSize < t.productionSize) := by sorry
