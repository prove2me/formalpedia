-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_mul_Ubar_le
-- name    : PaddedDescent.F.Arith.mul_Ubar_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:10.20005+00:00
-- url     : https://prove2.me/theorems/9f34d259-14c0-4844-8b9d-06f65b4cbf81
-- title:
--   Arith: mul Ubar le
-- statement:
--   800·Ubar ≤ 800g³Λ + 717g⁴Λ + 400g⁴ + 800.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L28-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L28-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithLevel
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.mul_Ubar_le (g lam : ℕ) :
    800 * Ubar g lam ≤ 800 * (g ^ 3 * lam) + 717 * (g ^ 4 * lam) + 400 * g ^ 4 + 800 := by sorry
