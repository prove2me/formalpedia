-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_log_constant
-- name    : ProbabilityTheory.leanlevy_chat22_semigroup_log_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:58:57.997993+00:00
-- url     : https://prove2.me/theorems/b404fc82-44da-4e85-8e34-8f83110a22cc
-- title:
--   A constant exponent from local logarithmic powers
-- statement:
--   The rescaled logarithms of all sufficiently small positive natural reciprocals agree, provided logarithms of the original semigroup scale on natural multiples near zero.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; Processes/LevyProcess.lean charFun_eq_exp_mul phase 3, original reciprocal argument.

import Mathlib
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat22_semigroup_log_constant
    (φ : ℝ≥0 → ℂ) (δ : ℝ≥0) (hδ_pos : 0 < δ)
    (hlog_pow : ∀ (n : ℕ) (s : ℝ≥0), (n : ℝ≥0) * s < δ →
      log (φ ((n : ℝ≥0) * s)) = ↑(n : ℤ) * log (φ s)) :
    ∃ c : ℂ, ∀ n : ℕ, 0 < n → (1 : ℝ≥0) / (n : ℝ≥0) < δ →
      ↑(n : ℤ) * log (φ (1 / (n : ℝ≥0))) = c := by sorry
