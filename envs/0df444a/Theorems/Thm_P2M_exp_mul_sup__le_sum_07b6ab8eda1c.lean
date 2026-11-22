-- Prove2me | Theorems.Thm_P2M_exp_mul_sup__le_sum_07b6ab8eda1c
-- name    : P2M_exp_mul_sup__le_sum_07b6ab8eda1c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:14.171797+00:00
-- url     : https://prove2.me/theorems/676e87d8-cb11-4606-867a-8914140cf951
-- title:
--   P2 M exp mul sup  le sum 07b6ab8eda1c: P2 M exp mul sup  le sum 07b6ab8eda1c
-- statement:
--   Soft-max bound: exp(t · Finset.sup') ≤ Σ exp(t · f_i).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L314-L324
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L314-L324

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem P2M_exp_mul_sup__le_sum_07b6ab8eda1c {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) (_ht : 0 ≤ t) :
    Real.exp (t * s.sup' hs f) ≤ ∑ i ∈ s, Real.exp (t * f i) := by sorry

alias «exp_mul_sup'_le_sum» := P2M_exp_mul_sup__le_sum_07b6ab8eda1c
