-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_mollifier_first_variation_bound
-- name    : TaoFivePrimes.eta0_mollifier_first_variation_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:53:57.175993+00:00
-- url     : https://prove2.me/theorems/efcdf289-4b56-4f0e-87d4-393df77caa6d
-- title:
--   Unit positive mollification preserves eta0 first variation bound
-- statement:
--   For a smooth compactly supported nonnegative real mollifier $\varphi$ of integral one, the smoothed logarithmic cutoff satisfies
--   $$\int_{\mathbb R}|(\eta_0*\varphi)'(x)|\,dx\le8\log2.$$
--   Together with the second-variation bound48, this supplies controlled derivative masses for the fixed-support smooth approximants used to extend the positive-parameter Proposition7.2 estimate to the nonsmooth cutoff.
-- source:
--   Tao arXiv1201.6656v4, (5.11) and mollification convention, p26; first-variation ingredient in eta0_smooth_inward_approximation. https://arxiv.org/pdf/1201.6656

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
open MeasureTheory
open scoped Convolution

theorem TaoFivePrimes.eta0_mollifier_first_variation_bound (φ : ℝ → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hp : ∀ x, 0 ≤ φ x) (hm : (∫ x, φ x) = 1) :
    (∫ x, |deriv (TaoFivePrimes.eta0 ⋆ φ) x|) ≤ 8 * Real.log 2 := by sorry
