-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_unit_numerator_bound
-- name    : TaoFivePrimes.theorem51_unit_numerator_bound
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-12T13:23:09.780217+00:00
-- url     : https://prove2.me/theorems/e1794571-24bf-41f1-8f08-9296fbea9a90
-- title:
--   Tao Theorem 5.1 with unit numerator: unoptimized modulus-two bound
-- statement:
--   Let $q\ge4$, let $a$ be an integer with $|a|=1$ and $(a,q)=1$, and suppose $4\alpha=a/q+\beta$ with $|\beta|\le q^{-2}$. Let $40\le U,V<x$, $UV\le x/4$, $UV^2\ge x$, and $UV<q-1$. Then
--
--   $$\begin{aligned}
--   |S_{\eta_0,2}(x,\alpha)|\le{}&\frac{96}{\pi^2}\frac{x}{(x/q)^2}\log(4x)\log\left(\frac{4eq}{\pi}\right)\\
--   &+\left(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\right)\log\left(\frac{x}{UV}\right)\log\left(\frac{Vx}{U}\right)\\
--   &+\left(0.55\frac{x}{\sqrt U}+0.78\frac{x}{\sqrt V}\right)\log\left(\frac{x}{U}\right).
--   \end{aligned}$$
--
--   This is the unit-numerator alternative in Tao's Theorem 5.1, before choosing the Vaughan parameters. It is an analytic source estimate for modulus two; it does not contain a change-of-modulus assumption, a large-denominator restriction, or the later specialization $U=x/V^2$. The Type I and Type II estimates needed to prove it remain an open obligation.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Theorem 5.1: equations (5.5) and (5.6), with (5.4) replaced by (5.7) under a=+/-1 and UV<q-1. https://arxiv.org/html/1201.6656v4#S5

import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem TaoFivePrimes.theorem51_unit_numerator_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
          Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) +
        (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q))) *
          Real.log (x / (U * V)) * Real.log (V * x / U) +
        (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) *
          Real.log (x / U) := by sorry
