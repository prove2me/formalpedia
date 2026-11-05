-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_four_mul_nRect_le
-- name    : PaddedDescent.F.Arith.four_mul_nRect_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:19.432541+00:00
-- url     : https://prove2.me/theorems/c82ed0fb-f5c5-4515-9cef-5463af8249f1
-- title:
--   Arith: four mul n Rect le
-- statement:
--   The number of rectangles is at most g⁴/4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L119-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L119-L119

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

theorem PaddedDescent.F.Arith.four_mul_nRect_le (g : ℕ) : 4 * Groundwork.Prog.nRect g ≤ g ^ 4 := by sorry
