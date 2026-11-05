-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_lamG_mul_le
-- name    : PaddedDescent.F.Arith.lamG_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:09.373493+00:00
-- url     : https://prove2.me/theorems/e74c40d3-9aa8-4c89-a2fb-5a15aeff5b5f
-- title:
--   Arith: lam G mul le
-- statement:
--   K³·lamG ≤ K³ + K·Ub + g·P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L30-L31

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

theorem PaddedDescent.F.Arith.lamG_mul_le (K g Ub P : ℕ) : lamG K g Ub P * K ^ 3 ≤ K ^ 3 + K * Ub + g * P := by sorry
