-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_fourier_second_variation_bound
-- name    : TaoFivePrimes.eta0_fourier_second_variation_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:12:18.403317+00:00
-- url     : https://prove2.me/theorems/7222e51c-b76a-44b4-acc3-7790c9423204
-- title:
--   Second-order Fourier decay of the literal eta0 cutoff
-- statement:
--   For every real nonzero frequency $\alpha$, Tao's logarithmic triangular cutoff satisfies
--
--   $$\left|\int_{\mathbb R}\eta_0(t)e(\alpha t)\,dt\right|\le\frac{48}{(2\pi\alpha)^2}.$$
--
--   The constant $48$ is the full total variation of the distributional second derivative, including all derivative jumps at $1/4,1/2,1$. This second-order estimate supplements the existing first-order Fourier bound and provides the nonsmooth integration-by-parts ingredient needed in the explicit-formula tail estimates. It applies directly to the literal cutoff, without pretending that it is twice continuously differentiable.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Lemma3.1 with k=2 and equation(5.13), including the distributional/mollification convention preceding (5.9); analytical ingredient in Proposition7.2. https://arxiv.org/pdf/1201.6656

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open MeasureTheory

theorem TaoFivePrimes.eta0_fourier_second_variation_bound (alpha : ℝ) (halpha : alpha ≠ 0) :
    ‖∫ t : ℝ, (TaoFivePrimes.eta0 t : ℂ) * TaoFivePrimes.expCircle (alpha * t)‖ ≤
      48 / (2 * Real.pi * alpha) ^ 2 := by sorry
