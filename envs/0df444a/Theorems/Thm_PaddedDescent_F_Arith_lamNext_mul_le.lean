-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_lamNext_mul_le
-- name    : PaddedDescent.F.Arith.lamNext_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:06.043134+00:00
-- url     : https://prove2.me/theorems/736a3d86-c1bf-4ecb-b5b8-9bb6ded1f49f
-- title:
--   Arith: lam Next mul le
-- statement:
--   D·K²·lamNext ≤ D·Ubar + 3g³Λ + 6g⁴Λ + D·K², with D = `Dcol`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L41-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L41-L50

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

theorem PaddedDescent.F.Arith.lamNext_mul_le (K g lam : ℕ) :
    Dcol * (K ^ 2 * lamNext K g lam) ≤ Dcol * Ubar g lam + 3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam) + Dcol * K ^ 2 := by sorry
