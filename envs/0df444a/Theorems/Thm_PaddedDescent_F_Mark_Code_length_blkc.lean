-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Code_length_blkc
-- name    : PaddedDescent.F.Mark.Code.length_blkc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:40.476406+00:00
-- url     : https://prove2.me/theorems/3af0346c-0eb0-463d-ad4a-593a4c89181a
-- title:
--   Code: length blkc
-- statement:
--   A block with j ones takes j·(1 + β) + 1 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L107-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L107-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Code
open Groundwork

theorem PaddedDescent.F.Mark.Code.length_blkc (β b : ℕ) (x : List Bool) (o : ℕ) : (blkc β b x o).length = (ones b x o).length * (1 + β) + 1 := by sorry
