-- Prove2me | Theorems.Thm_Parikh_ActivationOrder_of_forall_mem
-- name    : Parikh.ActivationOrder.of_forall_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:49:52.882057+00:00
-- url     : https://prove2.me/theorems/4b89adfb-ab3c-4f79-8e51-038683bbf22a
-- title:
--   Activation Order: of forall mem
-- statement:
--   If every requested root is already present, any finite order is enabled.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L85-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L85-L92

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

theorem Parikh.ActivationOrder.of_forall_mem {U : Set N} {cs : List C}
    (h : ∀ c ∈ cs, required c ∈ U) : ActivationOrder required added U cs := by sorry
