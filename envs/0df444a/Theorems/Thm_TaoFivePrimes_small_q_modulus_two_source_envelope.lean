-- Prove2me | Theorems.Thm_TaoFivePrimes_small_q_modulus_two_source_envelope
-- name    : TaoFivePrimes.small_q_modulus_two_source_envelope
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-09-12T12:47:20.95098+00:00
-- url     : https://prove2.me/theorems/c5a96811-5ab6-457f-a5fe-c396fe7e5580
-- title:
--   Small-q source envelope at modulus 2
-- statement:
--   Let $x\ge 10^{20}$ and suppose
--
--   $$4\alpha=\frac aq+\beta,\qquad 100\le q\le x/100,\qquad (a,q)=1,\qquad |\beta|\le q^{-2},\qquad q\le x^{1/3}.$$
--
--   For Tao's cutoff $\eta_0$, the modulus-two smoothed von Mangoldt sum satisfies
--
--   $$\begin{aligned}
--   |S_{\eta_0,2}(x,\alpha)|\le{}&\frac{x}{q}\log(2x)\left[\frac12\log\left(\frac{2x}{q^2}+4\right)+0.9(8+\log q)\right]\\
--   &+(0.301\log^2 q+2.66\log q)\frac{x}{\sqrt q}.
--   \end{aligned}$$
--
--   This is the small-denominator cancellation estimate before changing the coprimality modulus. It isolates the Vaughan Type I/II part of Tao's Section 6 derivation of (1.10).
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Theorem 5.1 (equations (5.4)-(5.6)) and Section 6 derivation of equation (1.10), https://arxiv.org/html/1201.6656v4

import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TaoFivePrimes

theorem small_q_modulus_two_source_envelope
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hsmall : (q : ℝ) ≤ x ^ (1 / 3 : ℝ)) :
    ‖smoothedExpSum eta0 2 x alpha‖ ≤
      (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
            0.9 * (8 + Real.log q)) +
        (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q) := by
  sorry

end TaoFivePrimes
