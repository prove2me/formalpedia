-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_fourier_decay_second_variation
-- name    : TaoFivePrimes.eta0_fourier_decay_second_variation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:27:34.042911+00:00
-- url     : https://prove2.me/theorems/1ee9c865-6276-4972-a70c-66648c301968
-- title:
--   Second-order Fourier decay of eta0 from variation forty-eight
-- statement:
--   For every nonzero real frequency $\beta$, the logarithmic triangular cutoff satisfies the second-order Fourier decay estimate
--
--   $$\left|\int_{\mathbb R}\eta_0(t)e(\beta t)\,dt\right|\le\frac{48}{(2\pi\beta)^2}.$$
--
--   The constant includes the total variation of the distributional second derivative: the classical density contributes $12$, and the derivative jumps contribute $16+16+4=36$. This gives the second-order integration-by-parts input for the explicit-formula major-arc estimates without incorrectly treating the nonsmooth cutoff as twice continuously differentiable. The existing first-order Fourier bound has numerator $8\log2$ and one power of frequency; this theorem supplies quadratic decay.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Fourier integration-by-parts principle Lemma3.1 and cutoff norms (5.11)-(5.13), with the distributional interpretation described on printed p.26; used in the Proposition7.2 analytic mechanism. https://arxiv.org/pdf/1201.6656

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open MeasureTheory

theorem TaoFivePrimes.eta0_fourier_decay_second_variation (beta : ℝ) (hbeta : beta ≠ 0) :
    ‖∫ t : ℝ, (TaoFivePrimes.eta0 t : ℂ) * TaoFivePrimes.expCircle (beta * t)‖ ≤
      48 / (2 * Real.pi * beta) ^ 2 := by sorry
