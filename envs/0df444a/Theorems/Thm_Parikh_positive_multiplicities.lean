-- Prove2me | Theorems.Thm_Parikh_positive_multiplicities
-- name    : Parikh.positive_multiplicities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T09:50:07.818928+00:00
-- url     : https://prove2.me/theorems/05e35e07-303e-4f20-beef-c089ed48bcb0
-- title:
--   Parikh: positive multiplicities
-- statement:
--   After activation, every positive multiplicity is possible (`lem:multiplicities`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L136-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/Activation.lean#L136-L177

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

theorem Parikh.positive_multiplicities {N C : Type*} [DecidableEq C]
    (required : C → N) (added : C → Set N) (U : Set N) (D : Finset C)
    (hself : ∀ c ∈ D, required c ∈ added c) (h : Activatable required added U D)
    (m : C → ℕ) (hm : ∀ c ∈ D, 0 < m c) :
    ∃ cs : List C, ActivationOrder required added U cs ∧
      (∀ c, c ∈ cs ↔ c ∈ D) ∧ (∀ c ∈ D, cs.count c = m c) := by sorry
