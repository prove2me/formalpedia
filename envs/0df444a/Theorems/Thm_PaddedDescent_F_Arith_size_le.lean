-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_size_le
-- name    : PaddedDescent.F.Arith.size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:47:42.730821+00:00
-- url     : https://prove2.me/theorems/0dba4f4c-2dbb-40ea-8961-e7eec2ffd0f9
-- title:
--   Arith: size le
-- statement:
--   The labels inside a class at the top: the exponent is at most X.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L50-L52

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

theorem PaddedDescent.F.Arith.size_le (hg : 0 < g) (hKg : K ≤ g) (hP : 4 * (g * P) ≤ K * X) : P ≤ X := by sorry
