-- Prove2me | Theorems.Thm_P2M_uc_does_not_imply_online__6055023e0fb5
-- name    : P2M_uc_does_not_imply_online__6055023e0fb5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:39:35.725558+00:00
-- url     : https://prove2.me/theorems/dcd8c14d-5481-4b58-98d0-34efbcb5f730
-- title:
--   P2 M uc does not imply online  6055023e0fb5: P2 M uc does not imply online  6055023e0fb5
-- statement:
--   Typeclass version of uc_does_not_imply_online.
--       Uses UniversallyMeasurableSpace to avoid threading ∀-quantified measurability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L170-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/GeneralizationResults.lean#L170-L178

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

theorem P2M_uc_does_not_imply_online__6055023e0fb5 (X : Type u) [MeasurableSpace X] [Infinite X]
    [UniversallyMeasurableSpace X] :
    ¬ (∀ (C : ConceptClass X Bool),
      HasUniformConvergence X C →
        ∃ (M : ℕ), MistakeBounded X Bool C M) := by sorry

alias «uc_does_not_imply_online'» := P2M_uc_does_not_imply_online__6055023e0fb5
