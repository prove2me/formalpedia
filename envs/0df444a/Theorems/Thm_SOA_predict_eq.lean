-- Prove2me | Theorems.Thm_SOA_predict_eq
-- name    : SOA_predict_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:00.817951+00:00
-- url     : https://prove2.me/theorems/f7c7144f-5da4-4d13-9ad5-15e2f2f65151
-- title:
--   SOA predict eq: SOA predict eq
-- statement:
--   SOA prediction: picks the label whose version space side has higher Ldim.
--       NOT @[simp]: proofs should explicitly opt-in to see SOA internals (Inv-stability).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L147-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GameInfra.lean#L147-L152

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
set_option autoImplicit true
@[expose] public section
public section

theorem SOA_predict_eq (X : Type) (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) :
    (SOA X C).predict history x =
      if LittlestoneDim X {c ∈ versionSpace C history | c x = true} ≥
         LittlestoneDim X {c ∈ versionSpace C history | c x = false}
      then true else false := by sorry
