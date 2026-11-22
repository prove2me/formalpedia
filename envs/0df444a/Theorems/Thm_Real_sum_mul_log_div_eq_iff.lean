-- Prove2me | Theorems.Thm_Real_sum_mul_log_div_eq_iff
-- name    : Real.sum_mul_log_div_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:33.577482+00:00
-- url     : https://prove2.me/theorems/cd7daa82-494f-441b-ae27-d9544cbd6c1a
-- title:
--   Real: sum mul log div eq iff
-- statement:
--   If equality holds in the previous bound, then $a_s=r\cdot b_s$ for every $s\in S$,
--   for some
--   constant $r\in \mathbb{R}$.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Analysis/SpecialFunctions/NegMulLog.lean#L116-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ZhangYeungInequality/PFR/Mathlib/Analysis/SpecialFunctions/NegMulLog.lean#L116-L152

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

theorem Real.sum_mul_log_div_eq_iff {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s,
  0 ≤ b i)
    (habs : ∀ i ∈ s, b i = 0 → a i = 0)
    (heq : ∑ i ∈ s, a i * log (a i / b i)
      = (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))) :
    ∃ r, ∀ i ∈ s, a i = r * (b i) := by sorry
