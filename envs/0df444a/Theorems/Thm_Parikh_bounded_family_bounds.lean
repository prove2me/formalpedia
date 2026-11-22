-- Prove2me | Theorems.Thm_Parikh_bounded_family_bounds
-- name    : Parikh.bounded_family_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:41.587567+00:00
-- url     : https://prove2.me/theorems/646bf024-555d-44d5-af77-63b20d15bfdd
-- title:
--   Parikh: bounded family bounds
-- statement:
--   Bounded families and leaf norms have the paper's coarse syntax bounds (`lem:count-trees`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L100-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L100-L145

module
public import Definitions.Def_LeanPool_Parikh_Activation
public import Mathlib.Data.Nat.Log
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_FiniteWitness
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Parikh_Construction
set_option autoImplicit true
@[expose] public section
public section
open Parikh

theorem Parikh.bounded_family_bounds {T : Type*} [Fintype T] [DecidableEq T]
    (g : ContextFreeGrammar T) :
    (∃ bases : Finset (ParseTree T g.NT),
      (∀ B, B ∈ bases ↔ IsBase g B) ∧ bases.card ≤ (grammarSize g).trees) ∧
    (∃ cycles : Finset (ParseTree T g.NT),
      (∀ C, C ∈ cycles ↔ IsBoundedCycle g C) ∧ cycles.card ≤ (grammarSize g).trees) ∧
    (∀ t, IsBase g t ∨ IsBoundedCycle g t → norm t.weight ≤ (grammarSize g).positions) := by sorry
