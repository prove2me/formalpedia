-- Prove2me | Theorems.Thm_Parikh_first_occurrences
-- name    : Parikh.first_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:01.873828+00:00
-- url     : https://prove2.me/theorems/ebb6ed0f-23ac-4897-864c-3e1799fdfaf2
-- title:
--   Parikh: first occurrences
-- statement:
--   A valid sequence's distinct first occurrences activate the same set (`lem:first-occurrence`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L115-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L115-L133

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

theorem Parikh.first_occurrences {N C : Type*} [DecidableEq C]
    (required : C → N) (added : C → Set N) (U : Set N) (cs : List C)
    (h : ActivationOrder required added U cs) :
    Activatable required added U cs.toFinset := by sorry
