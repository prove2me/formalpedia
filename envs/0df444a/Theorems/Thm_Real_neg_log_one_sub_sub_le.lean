-- Prove2me | Theorems.Thm_Real_neg_log_one_sub_sub_le
-- name    : Real.neg_log_one_sub_sub_le
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:39:28.085366+00:00
-- url     : https://prove2.me/theorems/abd65921-6858-4bcd-b65b-f202ab4d6338
-- title:
--   A quadratic bound for the logarithm remainder
-- statement:
--   For every real number $0\le x<1$,
--
--   $$
--   -\log(1-x)-x\le\frac{x^2}{2(1-x)}.
--   $$
--
--   This bounds the remainder after the linear term of the negative logarithm.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/Log/NegLogOneSub.lean#L52-L73), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/Log/NegLogOneSub.lean#L52-L73

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Elementary bounds on `-log (1 - x)`

This file bounds the quadratic remainder `-log (1 - x) - x`, then specializes the estimate to
`x = y ^ (-s)`. The sharp factor `2` in the denominator comes from reading Mathlib's complex
logarithm bound along the reals. It also records the coarser estimate
`-log (1 - x) ≤ x + 2 x ^ 2` for `0 ≤ x ≤ 1/2`.

## Main results

* `Real.neg_log_one_sub_sub_le`: for `0 ≤ x < 1`, the remainder is at most
  `x² / (2 (1 - x))`.
* `Real.neg_log_one_sub_rpow_sub_le_div`: for `2 ≤ y` and `0 < s`, it is at most
  `y ^ (-2s) / (2 (1 - 2 ^ (-s)))`.
* `Real.neg_log_one_sub_rpow_sub_le`: for `2 ≤ y` and `1 ≤ s`, it is at most `y⁻²`.
* `Real.neg_log_one_sub_le_add_two_mul_sq`: for `0 ≤ x ≤ 1/2`, `-log (1 - x)` is at most
  `x + 2 x ^ 2`.
* `Complex.norm_neg_log_one_sub_sub_le`: for complex `z` with `‖z‖ ≤ 1/2`, the remainder
  `-log (1 - z) - z` has norm at most `‖z‖ ^ 2`.

## References

The shape of `Real.neg_log_one_sub_sub_le` follows the private declaration
`neg_log_one_sub_sub_le` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
C. Birkbeck and R. Brasca), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The sharper
constant here comes from Mathlib's `Complex.norm_log_one_sub_inv_sub_self_le`.
-/

 section

namespace Real
end Real
section Real
open Real

theorem Real.neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -_root_.Real.log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x)) := by sorry
