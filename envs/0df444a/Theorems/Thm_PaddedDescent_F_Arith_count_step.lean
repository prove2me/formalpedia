-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_count_step
-- name    : PaddedDescent.F.Arith.count_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:55.35423+00:00
-- url     : https://prove2.me/theorems/2b3ce6f0-a078-44ac-914d-a534028e5870
-- title:
--   Arith: count step
-- statement:
--   The arithmetic of `Inv.step`, line `count`, with plain variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L88-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L88-L98

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

theorem PaddedDescent.F.Arith.count_step {cnt lam Rr L K2 G T : ℕ} (c1 : lam + 1 ≤ 2 ^ L) (O5 : Rr ≤ G) (O8c : 2 * K2 ≤ G)
    (h4 : cnt * 2 ^ (L * (2 * G)) ≤ T) : cnt * (lam + 1) ^ Rr * 2 ^ (L * (2 * K2)) ≤ T := by sorry
