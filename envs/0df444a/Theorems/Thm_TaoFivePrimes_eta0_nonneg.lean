-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_nonneg
-- name    : TaoFivePrimes.eta0_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-08T08:53:30.357778+00:00
-- url     : https://prove2.me/theorems/8c686a0b-841d-477c-a98b-cfd0d49ae051
-- title:
--   The cutoff $\eta_0$ is nonnegative
-- statement:
--   Tao's logarithmic cutoff $\eta_0(t) = 4(\log 2 - |\log 2t|)_+$, extended by zero to $t \leq 0$, is nonnegative everywhere. This is immediate from its definition as four times a maximum with zero, but it is worth having available: $\eta_0$ appears as a weight in the third prime sum of equation (8.10) and in the exponential sum $S_{\eta_0,q_0}$ of Theorem 1.3, and nonnegativity of the weights is what makes the representation count nonnegative and hence makes its positivity equivalent to the existence of a representation.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, equation (1.7).

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem eta0_nonneg (t : ℝ) : 0 ≤ eta0 t := by
  sorry

end TaoFivePrimes
