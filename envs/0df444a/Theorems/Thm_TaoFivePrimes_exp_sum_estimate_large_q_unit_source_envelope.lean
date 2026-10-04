-- Prove2me | Theorems.Thm_TaoFivePrimes_exp_sum_estimate_large_q_unit_source_envelope
-- name    : TaoFivePrimes.exp_sum_estimate_large_q_unit_source_envelope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-09T12:08:30.863309+00:00
-- url     : https://prove2.me/theorems/3d23bf2a-4938-4e21-a27c-2733e36173b1
-- title:
--   Tao (1.12): large-denominator source envelope
-- statement:
--   Let $x\ge 10^{20}$ and let $a/q$ approximate $4\alpha$ with $100\le q\le x/100$, $(a,q)=1$, $|4\alpha-a/q|\le q^{-2}$, $|a|=1$, and $q\ge x^{2/3}$. Let $q_0$ have no prime divisor greater than $\sqrt{x}$. For real parameters $U,V$ satisfying $U=x/V^2$, $V=1.02x/q$, $40\le U,V<x$, $UV\le x/4$, $x\le UV^2$, and $UV<q-1$, the smoothed von Mangoldt sum obeys
--   $$
--   \begin{aligned}
--   |S_{\eta_0,q_0}(x,\alpha)|\le{}&\frac{96}{\pi^2}\frac{x}{(x/q)^2}\log(4x)\log\!\left(\frac{4eq}{\pi}\right)\\
--   &+3\left(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\right)\log^2 V\\
--   &+2\left(0.55\frac{x}{\sqrt U}+0.78\frac{x}{\sqrt V}\right)\log V+20.16\sqrt x.
--   \end{aligned}
--   $$
--   This is the explicit Section 6 envelope obtained from Tao Theorem 5.1 and the special Type I estimate (5.7). The final term records the modulus change from $2$ to $q_0$ through modulus $1$.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 5 equations (5.5)-(5.7) and Section 6 proof of Theorem 1.3 equation (1.12), with Lemma 4.1: https://arxiv.org/html/1201.6656v4

import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TaoFivePrimes


theorem exp_sum_estimate_large_q_unit_source_envelope
    (x alpha beta U V : ℝ) (a : ℤ) (q q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x)
    (hlarge : x ^ (2 / 3 : ℝ) ≤ (q : ℝ))
    (hU : U = x / V ^ 2) (hV : V = 1.02 * x / q)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1) :
    ‖smoothedExpSum eta0 q0 x alpha‖ ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
          Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) +
        (0.1 * (x / Real.sqrt q) +
          0.39 * (x / Real.sqrt (x / q))) * 3 * Real.log V ^ 2 +
        (0.55 * (x / Real.sqrt U) +
          0.78 * (x / Real.sqrt V)) * 2 * Real.log V +
        20.16 * Real.sqrt x := by sorry

end TaoFivePrimes
