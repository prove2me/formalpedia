-- Prove2me | Theorems.Thm_TaoFivePrimes_theorem51_scale_bound_signed
-- name    : TaoFivePrimes.theorem51_scale_bound_signed
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-12T18:20:51.469361+00:00
-- url     : https://prove2.me/theorems/b111b484-f725-4569-8504-3d222a36c577
-- title:
--   Signed unit-numerator bound for the actual odd scale sum
-- statement:
--   Let q >= 100 be a natural number, W >= 40 and x/W >= 40, and write 4 alpha = a/q + beta with a an integer satisfying |a|=1 and |beta| <= 1/q^2. For arbitrary real cutoffs U,V, let F(W) denote the norm of the finite odd rectangular sum defined in TaoFivePrimes_Theorem51Scale. Then
--
--   $$F(W) \le \frac{1.1}{8}\sqrt{(W/4+2q)(x/(2Wq)+1)x}\log W.$$
--
--   This is the concrete pointwise estimate preceding the scale integration in Section 5.3, with both numerator signs included. It isolates finite exponential-sum analysis from integration. A complete Lean proof accompanies this node.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 5.3, equations (5.19)-(5.22) and the pointwise display immediately following (5.22). https://arxiv.org/html/1201.6656v4#S5.SS3

import Definitions.Def_TaoFivePrimes_Theorem51Scale
import Mathlib
open TaoFivePrimes

theorem TaoFivePrimes.theorem51_scale_bound_signed (x alpha beta U V W : ℝ) (a : ℤ) (q : ℕ)
    (hq : 100 ≤ q) (hW : 40 ≤ W) (hxW : 40 ≤ x / W)
    (ha : a.natAbs = 1) (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    ‖theorem51ScaleSum x alpha U V W‖ ≤
      (1.1 / 8) * Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) * Real.log W := by sorry
