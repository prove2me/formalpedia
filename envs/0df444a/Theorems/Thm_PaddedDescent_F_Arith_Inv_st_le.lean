-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Inv_st_le
-- name    : PaddedDescent.F.Arith.Inv.st_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:43.348799+00:00
-- url     : https://prove2.me/theorems/e838e591-e73a-4200-b063-7879780dce7d
-- title:
--   Inv: st le
-- statement:
--   The exponent of the settings of one group of the grouping, which has at most 2g/K nodes (as in
--   the proof of Lemma 1): Pn·(2g/K) ≤ 4·(X + Z).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L161-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L161-L167

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

theorem PaddedDescent.F.Arith.Inv.st_le (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) :
    Pn (gseq j) lam * (2 * gseq j / Kseq j) ≤ 4 * (X + Z) := by sorry
