-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_four_sq_mul_lamG_le
-- name    : PaddedDescent.F.Arith.four_sq_mul_lamG_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:48:57.412124+00:00
-- url     : https://prove2.me/theorems/701f930d-e551-4a95-be5e-719c75f6cf15
-- title:
--   Arith: four sq mul lam G le
-- statement:
--   With Q = K²·lamG: 4·Q ≤ 4·K² + 4·Ub + X, if 4·g·P ≤ K·X.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L34-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L34-L38

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

theorem PaddedDescent.F.Arith.four_sq_mul_lamG_le (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) :
    4 * (K ^ 2 * lamG K g Ub P) ≤ 4 * K ^ 2 + 4 * Ub + X := by sorry
