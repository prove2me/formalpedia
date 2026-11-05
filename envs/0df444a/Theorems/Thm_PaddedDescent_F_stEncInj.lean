-- Prove2me | Theorems.Thm_PaddedDescent_F_stEncInj
-- name    : PaddedDescent.F.stEncInj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:41:21.271518+00:00
-- url     : https://prove2.me/theorems/8ebf736a-a7a5-4428-83fb-5864e018e120
-- title:
--   F: st Enc Inj
-- statement:
--   For 0 < b ≤ 2^β a string of known length is read back from its code, whatever follows the code.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L159-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkCode.lean#L159-L159

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
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.stEncInj : StEncInj := by sorry
