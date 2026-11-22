-- Prove2me | Theorems.Thm_UniformMeasurableBatchFamily_pointwise
-- name    : UniformMeasurableBatchFamily.pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:46.622913+00:00
-- url     : https://prove2.me/theorems/e0e71699-695b-491b-a7b4-3ec855fc33d3
-- title:
--   Uniform Measurable Batch Family: pointwise
-- statement:
--   A uniform measurable batch family is pointwise measurable: each individual `L n`
--   belongs to `MeasurableBatchLearner`. The uniform property factors through the constant
--   index embedding `n ↦ (n, ·)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L137-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L137-L142

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem UniformMeasurableBatchFamily.pointwise
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool) [hL : UniformMeasurableBatchFamily L]
    (n : ℕ) : MeasurableBatchLearner X (L n) := by sorry
