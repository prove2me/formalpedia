-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_typeII_of_scale_bound
-- name    : TaoFivePrimes.theorem51_typeII_of_scale_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T18:21:09.428596+00:00
-- url     : https://prove2.me/theorems/b46d7b94-7c1d-4d9d-980f-18230c005f4c
-- title:
--   Scale integration reduction for the centered Type II bound
-- statement:
--   Under the parameter assumptions of the unit-numerator Type II estimate in Tao Theorem 5.1, suppose that the actual odd rectangular sum F(W) satisfies
--
--   $$F(W) \le \frac{1.1}{8}\sqrt{(W/4+2q)(x/(2Wq)+1)x}\log W$$
--
--   for every V <= W <= x/U. Then the public centered smoothed Type II sum satisfies the explicit Type II conclusion of Theorem 5.1, with coefficients 0.1, 0.39, 0.55 and 0.78.
--
--   This is the remaining integration step, not a proved theorem. The route is the eta_0 scale decomposition (5.19), support restriction (5.20), finite-sum/integral interchange, radical bounds in the unit regime, weighted logarithmic integration, and numerical rounding. The upper-end logarithm is log(x/U). The finite pointwise bound is an explicit hypothesis, to be discharged by the sibling scale theorem; no large-sieve estimate remains to prove in this node.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 5.3, equations (5.19)-(5.22) and the pointwise display immediately following (5.22). https://arxiv.org/html/1201.6656v4#S5.SS3

import Definitions.Def_TaoFivePrimes_Theorem51Scale
import Mathlib

theorem TaoFivePrimes.theorem51_typeII_of_scale_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1)
    (hscale : ∀ W : ℝ, V ≤ W → W ≤ x / U →
      ‖TaoFivePrimes.theorem51ScaleSum x alpha U V W‖ ≤
        (1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W) :
    TaoFivePrimes.theorem51TypeII x alpha U V ≤
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q))) *
        Real.log (x / (U * V)) * Real.log (V * x / U) +
      (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) *
        Real.log (x / U) := by sorry
