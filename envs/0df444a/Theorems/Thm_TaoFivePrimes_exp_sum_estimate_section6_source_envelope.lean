-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate_section6_source_envelope
-- name    : TaoFivePrimes.exp_sum_estimate_section6_source_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-09T12:00:32.040845+00:00
-- url     : https://prove2.me/theorems/e39d0b92-3205-4ca8-a9be-01c09b6c65ec
-- title:
--   Tao (1.9): Section 6 source envelope
-- statement:
--   Let $x\ge 10^{20}$ and suppose $a/q$ approximates $4\alpha$ with $100\le q\le x/100$, $(a,q)=1$, and $|4\alpha-a/q|\le q^{-2}$. Let every prime divisor of the auxiliary modulus $q_0$ be at most $\sqrt{x}$. Then the smoothed von Mangoldt sum satisfies
--   $$
--   \begin{aligned}
--   |S_{\eta_0,q_0}(x,\alpha)|\le{}&\left(0.4\frac{x}{q}+0.1\frac{x}{\sqrt q}+2.45\frac{x}{x/q}+0.39\frac{x}{\sqrt{x/q}}+0.149x^{4/5}\right)\\
--   &\qquad\times\log x\,(\log x+11.3)+20.16\sqrt{x}.
--   \end{aligned}
--   $$
--   The polynomial-logarithmic part is the explicit intermediate envelope in Tao Section 6 after specializing Theorem 5.1 to $U=x^{2/5}/4$ and $V=x^{2/5}/2$. The final term keeps visible the Lemma 4.1 cost of transferring from modulus $2$ to $q_0$ through modulus $1$.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 6, proof of Theorem 1.3 equation (1.9), using Theorem 5.1 and Lemma 4.1: https://arxiv.org/html/1201.6656v4

import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TaoFivePrimes

theorem exp_sum_estimate_section6_source_envelope
    (x alpha beta : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      (0.4 * (x / q) + 0.1 * (x / Real.sqrt q) +
          2.45 * (x / (x / q)) +
          0.39 * (x / Real.sqrt (x / q)) +
          0.149 * x ^ (4 / 5 : ℝ)) *
        Real.log x * (Real.log x + 11.3) +
      20.16 * Real.sqrt x := by sorry

end TaoFivePrimes
