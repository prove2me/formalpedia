-- Prove2me | Theorems.Thm_SOA_init_eq
-- name    : SOA_init_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:09.903249+00:00
-- url     : https://prove2.me/theorems/fd11c4d4-84a2-4897-b918-829f2b08b4c6
-- title:
--   SOA init eq: SOA init eq
-- statement:
--   SOA init state is empty history.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L161-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L161-L162

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem SOA_init_eq (X : Type) (C : ConceptClass X Bool) :
    (SOA X C).init = ([] : List (X × Bool)) := by sorry
