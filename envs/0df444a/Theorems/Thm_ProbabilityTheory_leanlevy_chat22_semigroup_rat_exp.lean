-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_rat_exp
-- name    : ProbabilityTheory.leanlevy_chat22_semigroup_rat_exp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:00:39.257338+00:00
-- url     : https://prove2.me/theorems/937ced52-20ed-4ea8-83a9-f67aa1d6e251
-- title:
--   Rational-time exponential representation of a complex semigroup
-- statement:
--   A nonvanishing complex semigroup satisfying natural and rational power laws and a locally constant rescaled logarithm agrees with a complex exponential at every nonnegative rational time.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4; Processes/LevyProcess.lean charFun_eq_exp_mul phase 4, original reciprocal-time proof.

import Mathlib
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat22_semigroup_rat_exp
    (φ : ℝ≥0 → ℂ) (δ : ℝ≥0) (c : ℂ) (N : ℕ)
    (hN_pos : 0 < N) (hN_small : (1 : ℝ≥0) / (N : ℝ≥0) < δ)
    (hφ_ne : ∀ t, φ t ≠ 0)
    (hφ_pow : ∀ (n : ℕ) (s : ℝ≥0), φ ((n : ℝ≥0) * s) = (φ s) ^ n)
    (hφ_rat : ∀ (k n : ℕ), φ ((k : ℝ≥0) / (n : ℝ≥0)) = (φ (1 / (n : ℝ≥0))) ^ k)
    (hconst : ∀ n : ℕ, 0 < n → (1 : ℝ≥0) / (n : ℝ≥0) < δ →
      ↑(n : ℤ) * log (φ (1 / (n : ℝ≥0))) = c) :
    ∀ (k n : ℕ), 0 < n → φ ((k : ℝ≥0) / (n : ℝ≥0)) =
      exp (c * ↑((k : ℝ) / (n : ℝ))) := by sorry
