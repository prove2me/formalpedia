-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Inv_lab_le
-- name    : PaddedDescent.F.Arith.Inv.lab_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:57.079214+00:00
-- url     : https://prove2.me/theorems/765921d6-3a89-4d47-8c57-4414ef23d59e
-- title:
--   Inv: lab le
-- statement:
--   The exponent of the labels of one node inside a group: Pn ≤ 2·(X + Z).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L170-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L170-L176

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}

theorem PaddedDescent.F.Arith.Inv.lab_le (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) : Pn (gseq j) lam ≤ 2 * (X + Z) := by sorry
