-- Prove2me | Theorems.Thm_Real_sum_mul_log_div_leq
-- name    : Real.sum_mul_log_div_leq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:27:44.095809+00:00
-- url     : https://prove2.me/theorems/42cba156-8e8e-4725-86ca-1eab82f2935f
-- title:
--   Real: sum mul log div leq
-- statement:
--   If $S$ is a finite set, and $a_s$, $b_s$ are non-negative for $s\in S$, then
--     $$\sum_{s\in S} a_s \log\frac{a_s}{b_s}\ge
--       \left(\sum_{s\in S}a_s\right)\log\frac{\sum_{s\in S} a_s}{\sum_{s\in S} b_s}$$.
--     We require additionally that, if $b_s=0$, then $s_s=0$ as otherwise the right hand
--     side should
--     morally be infinite, which it can't be in the formalization using real numbers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Analysis/SpecialFunctions/NegMulLog.lean#L39-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Analysis/SpecialFunctions/NegMulLog.lean#L39-L80

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Analysis_SpecialFunctions_NegMulLog
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal NNReal Topology
open Real
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {p : ι → ℝ}

theorem Real.sum_mul_log_div_leq {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s,
  0 ≤ b i)
    (habs : ∀ i ∈ s, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) ≤ ∑ i ∈ s,
      a i * log (a i / b i) := by sorry
