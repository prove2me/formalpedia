-- Prove2me | Theorems.Thm_SOA_update_eq
-- name    : SOA_update_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:04.646951+00:00
-- url     : https://prove2.me/theorems/b60d5cdd-093b-4d48-85a1-4fb1384f60bf
-- title:
--   SOA update eq: SOA update eq
-- statement:
--   SOA state update: append observation to history.
--       NOT @[simp]: explicit use preserves abstraction barrier.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L156-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L156-L158

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem SOA_update_eq (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) (y : Bool) :
    (SOA X C).update history x y = history ++ [(x, y)] := by sorry
