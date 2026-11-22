-- Prove2me | Theorems.Thm_P2M_consistent_learner_pac__01cd7c3e2f93
-- name    : P2M_consistent_learner_pac__01cd7c3e2f93
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:37.367688+00:00
-- url     : https://prove2.me/theorems/2ff747e4-a5bf-4fc2-bee2-d4964f11d325
-- title:
--   P2 M consistent learner pac  01cd7c3e2f93: P2 M consistent learner pac  01cd7c3e2f93
-- statement:
--   Typeclass version of consistent_learner_pac.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L207-L214
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L207-L214

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem P2M_consistent_learner_pac__01cd7c3e2f93 (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] (hvcdim : VCDim X C < ⊤)
    (L : BatchLearner X Bool)
    (hcons : ∀ {m : ℕ} (S : Fin m → X × Bool), ∀ i, L.learn S (S i).1 = (S i).2) :
    PACLearnable X C := by sorry

alias «consistent_learner_pac'» := P2M_consistent_learner_pac__01cd7c3e2f93
