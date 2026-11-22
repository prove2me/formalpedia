-- Prove2me | Theorems.Thm_P2M_sample_complexity_lower_bound__78d3c3e91a01
-- name    : P2M_sample_complexity_lower_bound__78d3c3e91a01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:41.791957+00:00
-- url     : https://prove2.me/theorems/c7b619ff-9593-45fc-bf11-663b5d5545d3
-- title:
--   P2 M sample complexity lower bound  78d3c3e91a01: P2 M sample complexity lower bound  78d3c3e91a01
-- statement:
--   Typeclass version of sample_complexity_lower_bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L246-L253
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L246-L253

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

theorem P2M_sample_complexity_lower_bound__78d3c3e91a01 (X : Type u) [MeasurableSpace X] [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) [MeasurableConceptClass X C] (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1 / 7) (hd_pos : 1 ≤ d) :
    Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ := by sorry

alias «sample_complexity_lower_bound'» := P2M_sample_complexity_lower_bound__78d3c3e91a01
