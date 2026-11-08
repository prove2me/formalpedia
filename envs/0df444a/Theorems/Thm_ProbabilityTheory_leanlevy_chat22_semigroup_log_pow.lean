-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat22_semigroup_log_pow
-- name    : ProbabilityTheory.leanlevy_chat22_semigroup_log_pow
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:51:44.532942+00:00
-- url     : https://prove2.me/theorems/459dc5d2-9f9e-4313-8754-30bcd7c62e54
-- title:
--   Local logarithmic powers for a continuous complex semigroup
-- statement:
--   A non-vanishing multiplicative complex semigroup continuous at zero has a locally additive principal logarithm, so its logarithm scales linearly under natural multiples sufficiently near zero.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; Processes/LevyProcess.lean charFun_eq_exp_mul Phase 1 and 2 around lines 300–341, source-exact analytic argument isolated.

import Mathlib
open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem ProbabilityTheory.leanlevy_chat22_semigroup_log_pow
    (φ : ℝ≥0 → ℂ) (hφ0 : φ 0 = 1) (hφ_ne : ∀ t, φ t ≠ 0)
    (hφ_mul : ∀ s k, φ (s + k) = φ s * φ k)
    (hφ_tendsto0 : Tendsto φ (𝓝 (0 : ℝ≥0)) (𝓝 1)) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ (n : ℕ) (s : ℝ≥0), (n : ℝ≥0) * s < δ →
        log (φ ((n : ℝ≥0) * s)) = ↑(n : ℤ) * log (φ s) := by sorry
