-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_eq_of_blkc
-- name    : PaddedDescent.F.Mark.Code.eq_of_blkc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:33.133488+00:00
-- url     : https://prove2.me/theorems/1e601758-0496-47fc-89e9-50281b8464b6
-- title:
--   Code: eq of blkc
-- statement:
--   One block is read back, whatever follows it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L67-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L67-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork

theorem PaddedDescent.F.Mark.Code.eq_of_blkc {β b : ℕ} (hb : b ≤ 2 ^ β) {x x' : List Bool} {o : ℕ} {r r' : List Bool}
    (h : blkc β b x o ++ r = blkc β b x' o ++ r') : ones b x o = ones b x' o ∧ r = r' := by sorry
