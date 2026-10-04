-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeII_bound
-- name    : TaoFivePrimes.theorem51_typeII_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T17:07:51.93749+00:00
-- url     : https://prove2.me/theorems/605a083b-e6e1-4471-b532-c6f34ea1a76a
-- title:
--   Unit-numerator centered Type II estimate for Tao Theorem 5.1
-- statement:
--   Assume q≥4, (a,q)=1, |a|=1, 4α=a/q+β, |β|≤q⁻², U,V≥40, U,V<x, UV≤x/4, x≤UV² and UV<q−1. The centered Type II sum obeys
--
--   $$T_{II}\le\left(0.1\frac{x}{\sqrt q}+0.39\frac{x}{\sqrt{x/q}}\right)\log\frac{x}{UV}\log\frac{Vx}{U}+\left(0.55\frac{x}{\sqrt U}+0.78\frac{x}{\sqrt V}\right)\log\frac{x}{U}.$$
--
--   This is the remaining bilinear analytic estimate. The centered coefficient and the literal odd sums are defined in the imported interface; no bilinear estimate is assumed in that definition.
-- source:
--   Tao, arXiv:1201.6656v4, Section 5.3, Type II estimate contributing equations (5.5) and (5.6), specialized to the unit-numerator hypotheses. https://arxiv.org/html/1201.6656v4#S5.SS3

import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem TaoFivePrimes.theorem51_typeII_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1) :
    TaoFivePrimes.theorem51TypeII x alpha U V ≤
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q))) *
        Real.log (x / (U * V)) * Real.log (V * x / U) +
      (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) *
        Real.log (x / U) := by sorry
