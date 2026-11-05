-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Inv_mul_le
-- name    : PaddedDescent.F.Arith.Inv.mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:44:24.499012+00:00
-- url     : https://prove2.me/theorems/f69e95cb-6bab-40af-bfd5-828c170d6deb
-- title:
--   Inv: mul le
-- statement:
--   From the invariant at level j: K_j·Λ ≤ X + Z.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L134-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L134-L144

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

theorem PaddedDescent.F.Arith.Inv.mul_le (h : Inv t X Z Qm Wm L j lam B cnt) : Kseq j * lam ≤ X + Z := by sorry
