-- Prove2me | Theorems.Thm_Value_stSameBlock
-- name    : Value.stSameBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:04:27.609199+00:00
-- url     : https://prove2.me/theorems/2079e23c-5582-4254-9792-850003149520
-- title:
--   Value: st Same Block
-- statement:
--   «both W̃_γ and W̃_γ' read θ_{a,b} from the same block of this string, so θ_{a,b} = θ_{b,a}».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L56-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L56-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

theorem Value.stSameBlock : StSameBlock := by sorry
