-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_mul_div_le
-- name    : PaddedDescent.F.Arith.mul_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:47:58.00798+00:00
-- url     : https://prove2.me/theorems/632fd316-461e-41d3-b551-2977ab46ea47
-- title:
--   Arith: mul div le
-- statement:
--   The states of a class at the top: the exponent is at most X.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L41-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L41-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithTop
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {K g Ub P X : ℕ}

theorem PaddedDescent.F.Arith.mul_div_le (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) : P * (2 * g / K) ≤ X := by sorry
