-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_fourier_decay_variation_source
-- name    : TaoFivePrimes.eta0_fourier_decay_variation_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-09T14:08:24.463089+00:00
-- url     : https://prove2.me/theorems/73bf2d0e-dd5b-446a-9500-d720e24dd115
-- title:
--   Lemma 3.3 Fourier decay for the logarithmic cutoff
-- statement:
--   Let $\eta_0(t)=4\max(0,\log 2-|\log(2t)|)$ for $t>0$, extended by zero. For every nonzero real frequency $u$, its positive-phase Fourier integral satisfies $$\left|\int_{\mathbb R}\eta_0(t)e^{2\pi iut}\,dt\right|\le \frac{8\log 2}{2\pi |u|}.$$ The coefficient $8\log 2$ is the total variation of the derivative on the two smooth pieces $[1/4,1/2]$ and $[1/2,1]$. This deterministic Fourier-analysis input contains no prime-number assertion.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Lemma 3.3 (equation (3.16)) and the specialization in Section 8 immediately after equation (8.19), https://arxiv.org/abs/1201.6656

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Mathlib

open MeasureTheory

namespace TaoFivePrimes

theorem eta0_fourier_decay_variation_source (u : ℝ) (hu : u ≠ 0) :
    norm (∫ t : ℝ, (eta0 t : ℂ) * expCircle (u * t)) ≤
      8 * Real.log 2 / (2 * Real.pi * |u|) := by
  sorry

end TaoFivePrimes
