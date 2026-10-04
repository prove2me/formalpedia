-- Prove2me | Theorems.Thm_TaoFivePrimes_eta1_nonneg
-- name    : TaoFivePrimes.eta1_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-08T08:53:44.874763+00:00
-- url     : https://prove2.me/theorems/e28eeca0-42a2-461f-a45b-09f5d5afa205
-- title:
--   The cutoff $\eta_1$ is nonnegative
-- statement:
--   The trapezoidal cutoff $\eta_1(t) = (1 - 10\,\mathrm{dist}(t,[1/5,4/5]))_+$, used for the first two primes in Section 8, is nonnegative everywhere. Immediate from its definition as a maximum with zero. It is the companion to the nonnegativity of $\eta_0$, and together they give nonnegativity of every weight in the representation count of equation (8.10).
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997-1038, https://arxiv.org/abs/1201.6656, Section 8, the definition of eta_1 at the start of the section.

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
open TaoFivePrimes

namespace TaoFivePrimes

theorem eta1_nonneg (t : ℝ) : 0 ≤ eta1 t := by
  sorry

end TaoFivePrimes
