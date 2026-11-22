-- Prove2me | Theorems.Thm_UniversallyMeasurableSpace_concept_measurable
-- name    : UniversallyMeasurableSpace.concept_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:19.462233+00:00
-- url     : https://prove2.me/theorems/649386e1-bdf5-4cc0-9390-ee69f10a701a
-- title:
--   Universally Measurable Space: concept measurable
-- statement:
--   The Universally Measurable Space construction uses the concept measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Measurability.lean#L147-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Measurability.lean#L147-L150

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
set_option autoImplicit true
@[expose] public section
public section
universe u

theorem UniversallyMeasurableSpace.concept_measurable
    {X : Type u} [MeasurableSpace X] [h : UniversallyMeasurableSpace X]
    (c : Concept X Bool) : Measurable c := by sorry
