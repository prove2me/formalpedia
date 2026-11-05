-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_mul_lamG_le
-- name    : PaddedDescent.F.Arith.mul_lamG_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:46.800748+00:00
-- url     : https://prove2.me/theorems/c44d5db2-c755-46bf-a895-1b2db7b389e6
-- title:
--   Arith: mul lam G le
-- statement:
--   The index of a table at the top: the exponent is at most K + 2·X + r, if Ub ≤ K·X + r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L55-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L55-L61

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

theorem PaddedDescent.F.Arith.mul_lamG_le {r : ℕ} (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) (hU : Ub ≤ K * X + r) :
    (K - 1) * lamG K g Ub P ≤ K + 2 * X + r := by sorry
