-- Prove2me | Theorems.Thm_TaoFivePrimes_small_q_modulus_transfer_source_envelope
-- name    : TaoFivePrimes.small_q_modulus_transfer_source_envelope
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-09-12T12:47:11.80613+00:00
-- url     : https://prove2.me/theorems/cba0b2b8-5272-44e3-8764-6f3c559ebc64
-- title:
--   Transfer the small-q estimate from modulus 2 to q₀
-- statement:
--   Let $x\ge 10^{20}$ and let $q_0>0$. Assume every prime divisor of $q_0$ is at most $\sqrt{x}$. Then Tao's smoothed sums with coprimality moduli $q_0$ and $2$ differ by at most
--
--   $$
--   \left|S_{\eta_0,q_0}(x,\alpha)-S_{\eta_0,2}(x,\alpha)\right|\le 20.16\sqrt{x}.
--   $$
--
--   The estimate isolates the elementary modulus-transfer step used after the modulus-two exponential-sum estimate. A term changed by the coprimality filter is a prime power; Tao's Lemma 4.1 controls the prime-power contribution, and the explicit constant is obtained with the Chebyshev bound for primes up to $\sqrt{x}$.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Lemma 4.1 and the Section 6 passage transferring the modulus-2 estimate to q_0; explicit Chebyshev input Mathlib NumberTheory.Chebyshev, theorem theta_le_log4_mul_x, https://arxiv.org/html/1201.6656v4

import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TaoFivePrimes

theorem small_q_modulus_transfer_source_envelope
    (x alpha : ℝ) (q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq0pos : 0 < q0)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q0 x alpha - smoothedExpSum eta0 2 x alpha‖ ≤
      20.16 * Real.sqrt x := by
  sorry

end TaoFivePrimes
