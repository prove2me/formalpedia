-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Inv_work_le
-- name    : PaddedDescent.F.Arith.Inv.work_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:50.801752+00:00
-- url     : https://prove2.me/theorems/188863e1-0ac8-498e-8fa9-ff1ee647d171
-- title:
--   Inv: work le
-- statement:
--   The work list at level j: cnt·instLen K_j Λ B + 2 ≤ 2^(2·L·K_t² + X + Z + Lw + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L201-L233
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L201-L233

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

theorem PaddedDescent.F.Arith.Inv.work_le {Lw : ℕ} (hLw : Kseq t * (3 * Wm + 14) + 4 * Qm + 10 ≤ 2 ^ Lw) (hj : j ≤ t)
    (h : Inv t X Z Qm Wm L j lam B cnt) :
    cnt * instLen (Kseq j) lam B + 2 ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw + 1) := by sorry
