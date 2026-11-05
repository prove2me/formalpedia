-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Inv_pat_le
-- name    : PaddedDescent.F.Arith.Inv.pat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:47.264024+00:00
-- url     : https://prove2.me/theorems/9bf982dd-90f6-4270-9e29-a158b6fb46ed
-- title:
--   Inv: pat le
-- statement:
--   The patterns of one instance: (Λ+1)^nRect g ≤ 2^(L·K_t²).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L179-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L179-L191

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

theorem PaddedDescent.F.Arith.Inv.pat_le (hL : Qm + 1 ≤ 2 ^ L) (hj : j + 1 ≤ t) (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) :
    (lam + 1) ^ nRect (gseq j) ≤ 2 ^ (L * Kseq t ^ 2) := by sorry
