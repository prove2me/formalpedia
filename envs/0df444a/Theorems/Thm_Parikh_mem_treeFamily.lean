-- Prove2me | Theorems.Thm_Parikh_mem_treeFamily
-- name    : Parikh.mem_treeFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:48:39.035816+00:00
-- url     : https://prove2.me/theorems/4d52c7e3-6f42-402f-92fc-19d4e7fc169e
-- title:
--   Parikh: mem tree Family
-- statement:
--   Every bounded active open tree belongs to the counting family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L108-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedFamilySupport.lean#L108-L136

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
set_option autoImplicit true
@[expose] public section
public section
open Parikh
variable {T : Type*} [Fintype T]

theorem Parikh.mem_treeFamily (g : ContextFreeGrammar T) (H : ℕ) (t : ParseTree T g.NT)
    (ht : ActiveOpen g t) (hh : t.height ≤ H) : t ∈ treeFamily g H := by sorry
