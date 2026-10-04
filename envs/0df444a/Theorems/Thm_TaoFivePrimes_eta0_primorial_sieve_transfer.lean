-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_primorial_sieve_transfer
-- name    : TaoFivePrimes.eta0_primorial_sieve_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-09T15:23:35.040251+00:00
-- url     : https://prove2.me/theorems/f17d0f4a-0d1a-4df2-bc77-c551df334e99
-- title:
--   Direct primorial-sieve transfer for the eta0 exponential sum
-- statement:
--   Let $x\ge 8.7\times 10^{36}$ and put $y=x/1000$. For the logarithmic cutoff $\eta_0$, changing the smoothed von Mangoldt sum from modulus $1$ to the primorial of $\lfloor\sqrt{x/1000}\rfloor$ changes its value by at most $9\times 10^{-8}y$, uniformly in the real frequency. This is the specialized sieve-modulus transfer used after Proposition 7.2.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 4, Lemma 4.1, specialized to eta0 and q=(sqrt(x/1000))#, https://arxiv.org/abs/1201.6656

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
open scoped BigOperators ArithmeticFunction.vonMangoldt
open MeasureTheory

namespace TaoFivePrimes

theorem eta0_primorial_sieve_transfer
    (x : ℕ) (h1 : 87 * 10 ^ 35 ≤ x) (theta : ℝ) :
    let y : ℝ := (x : ℝ) / 1000
    ‖smoothedExpSum eta0 (primorial (Nat.sqrt (x / 1000))) y theta -
        smoothedExpSum eta0 1 y theta‖ ≤
      (9 : ℝ) / 10 ^ 8 * y := by sorry

end TaoFivePrimes
