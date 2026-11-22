-- Prove2me | Theorems.Thm_Parikh_ActivationOrder_filter_of_covered
-- name    : Parikh.ActivationOrder.filter_of_covered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:51.515741+00:00
-- url     : https://prove2.me/theorems/29dabec3-0141-4c40-9015-128f46504126
-- title:
--   Activation Order: filter of covered
-- statement:
--   An operation may be omitted when everything it adds is already present.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L63-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L63-L82

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

theorem Parikh.ActivationOrder.filter_of_covered {U : Set N} {cs : List C}
    (h : ActivationOrder required added U cs) (p : C → Bool)
    (hcovered : ∀ c ∈ cs, p c = false → added c ⊆ U) :
    ActivationOrder required added U (cs.filter p) := by sorry
