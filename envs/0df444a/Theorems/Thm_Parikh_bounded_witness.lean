-- Prove2me | Theorems.Thm_Parikh_bounded_witness
-- name    : Parikh.bounded_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:51:39.244807+00:00
-- url     : https://prove2.me/theorems/629e36f8-8981-410a-be11-93afb0691417
-- title:
--   Parikh: bounded witness
-- statement:
--   The guaranteed exact witness also satisfies all four bounds (`thm:size-bound`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L171-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Construction.lean#L171-L185

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

theorem Parikh.bounded_witness {T : Type*} [Fintype T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language ∧ WithinBounds (grammarSize g) W := by sorry
