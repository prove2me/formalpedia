-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_six_cube_mul_cube_le
-- name    : PaddedDescent.F.Arith.six_cube_mul_cube_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:26.133347+00:00
-- url     : https://prove2.me/theorems/b7ebef8a-9f4e-4703-a342-4a445c2ef07f
-- title:
--   Arith: six cube mul cube le
-- statement:
--   6g³·K³ ≤ (g·g)³, if 2K ≤ g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L146-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L146-L152

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

theorem PaddedDescent.F.Arith.six_cube_mul_cube_le {K g : ℕ} (hg : 2 * K ≤ g) : 6 * g ^ 3 * K ^ 3 ≤ (g * g) ^ 3 := by sorry
