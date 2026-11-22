-- Prove2me | Theorems.Thm_Parikh_ActivationOrder_append_of_covered
-- name    : Parikh.ActivationOrder.append_of_covered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:54.05004+00:00
-- url     : https://prove2.me/theorems/0dd732f3-56e8-473a-8c2e-4e778da1d846
-- title:
--   Activation Order: append of covered
-- statement:
--   After an activation pass, append any operations whose roots it supplies.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L95-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L95-L111

module
public import Definitions.Def_LeanPool_Parikh_Decomposition
public import Definitions.Def_LeanPool_Parikh_InsertionSequences
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Order.Group.Nat
public import Definitions.Def_LeanPool_Parikh_Activation
set_option autoImplicit true
@[expose] public section
public section
open Parikh
open Parikh.ActivationOrder
variable {N C : Type*} {required : C → N} {added : C → Set N}

theorem Parikh.ActivationOrder.append_of_covered {U : Set N} {cs ds : List C}
    (h : ActivationOrder required added U cs)
    (hcovered : ∀ d ∈ ds, required d ∈ U ∨ ∃ c ∈ cs, required d ∈ added c) :
    ActivationOrder required added U (cs ++ ds) := by sorry
