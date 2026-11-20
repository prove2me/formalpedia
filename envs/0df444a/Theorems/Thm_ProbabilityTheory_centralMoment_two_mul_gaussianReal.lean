-- Prove2me | Theorems.Thm_ProbabilityTheory_centralMoment_two_mul_gaussianReal
-- name    : ProbabilityTheory.centralMoment_two_mul_gaussianReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:05:56.939618+00:00
-- url     : https://prove2.me/theorems/be2c9fa5-e354-4f5e-9668-f9a380fc63e3
-- title:
--   centralMoment two mul gaussianReal
-- statement:
--   The source theorem `ProbabilityTheory.centralMoment_two_mul_gaussianReal` is extracted from `BrownianMotion.Gaussian.Moment`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Distributions.Gaussian.Real


@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

theorem _root_.ProbabilityTheory.centralMoment_two_mul_gaussianReal (μ : ℝ) (σ : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (gaussianReal μ (σ^2))
    = σ ^ (2 * n) * Nat.doubleFactorial (2 * n - 1) := by sorry
