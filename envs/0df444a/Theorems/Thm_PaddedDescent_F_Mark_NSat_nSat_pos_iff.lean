-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_NSat_nSat_pos_iff
-- name    : PaddedDescent.F.Mark.NSat.nSat_pos_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:44:11.86569+00:00
-- url     : https://prove2.me/theorems/c36f8564-e85b-4b32-857e-10623f2a4b92
-- title:
--   NSat: n Sat pos iff
-- statement:
--   A formula on variables below n has a satisfying assignment of these n variables exactly if it is
--   satisfiable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/NSat.lean#L19-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/NSat.lean#L19-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkMath
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_PaddedDescent_F_NSat
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.NSat
open Groundwork Groundwork.Prog

theorem PaddedDescent.F.Mark.NSat.nSat_pos_iff {n : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) : 0 < nSat n x ↔ Fml.Sat x := by sorry
