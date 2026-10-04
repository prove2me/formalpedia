-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate_small_q_source_envelope
-- name    : TaoFivePrimes.exp_sum_estimate_small_q_source_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-09T11:00:08.061433+00:00
-- url     : https://prove2.me/theorems/f93c4db9-21be-46a1-866d-73e024b79967
-- title:
--   Small-denominator exponential-sum source envelope
-- statement:
--   Let $x\ge10^{20}$ and let $4\alpha=a/q+\beta$, where $100\le q\le x/100$, $(a,q)=1$, $|\beta|\le q^{-2}$, and $q\le x^{1/3}$. If every prime factor of $q_0$ is at most $\sqrt{x}$, then the smoothed exponential sum obeys the Section 6 source envelope
--
--   $$\begin{aligned}|S_{\eta_0,q_0}(x,\alpha)|\le{}&\frac{x}{q}\log(2x)\left[0.5\log\left(\frac{2x}{q^2}+4\right)+0.9(8+\log q)\right]\\&+(0.301\log^2q+2.66\log q)\frac{x}{\sqrt q}+20.16\sqrt x.\end{aligned}$$
--
--   The first two terms are Tao's bound after applying Theorem 5.1 with $U=x/q^2$ and $V=q$. The final explicit term safely transfers the modulus-$2$ estimate to $q_0$ using Lemma 4.1 twice.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Lemma 4.1, Theorem 5.1 (equations 5.4-5.6), and Section 6 derivation of equation (1.10), https://arxiv.org/html/1201.6656v4

import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TaoFivePrimes

theorem exp_sum_estimate_small_q_source_envelope
    (x alpha beta : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hsmall : (q : ℝ) ≤ x ^ (1 / 3 : ℝ)) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      (x / q) * Real.log (2 * x) *
          (0.5 * Real.log (2 * x / (q : ℝ) ^ 2 + 4) +
            0.9 * (8 + Real.log q)) +
        (0.301 * Real.log q ^ 2 + 2.66 * Real.log q) *
          (x / Real.sqrt q) +
        20.16 * Real.sqrt x := by
  sorry

end TaoFivePrimes
