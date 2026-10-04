-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_mollifier_second_variation_bound
-- name    : TaoFivePrimes.eta0_mollifier_second_variation_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:51:23.218187+00:00
-- url     : https://prove2.me/theorems/87dba18e-eeee-4062-8152-69de4021e444
-- title:
--   Unit positive mollification preserves eta0 second variation at most forty-eight
-- statement:
--   If $\varphi$ is a smooth compactly supported nonnegative real function of integral one, then the mollification $F=\eta_0*\varphi$ satisfies
--   $$\int_{\mathbb R}|F''(x)|\,dx\le48.$$
--   This is the crucial second-derivative estimate for fixed-support smooth approximants of the nonsmooth cutoff. The constant48 includes the variation36 from derivative jumps and12 from the classical second-derivative density, rather than only the classical derivative integral.
-- source:
--   Tao arXiv1201.6656v4, mollification convention and (5.13), p26. Input to eta0_smooth_inward_approximation in the Proposition7.2 mission frontier. https://arxiv.org/pdf/1201.6656

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
open MeasureTheory
open scoped Convolution

theorem TaoFivePrimes.eta0_mollifier_second_variation_bound (φ : ℝ → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hp : ∀ x, 0 ≤ φ x) (hm : (∫ x, φ x) = 1) :
    (∫ x, |deriv (deriv (TaoFivePrimes.eta0 ⋆ φ)) x|) ≤ 48 := by sorry
