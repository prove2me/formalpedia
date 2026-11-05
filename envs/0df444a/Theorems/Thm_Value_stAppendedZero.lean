-- Prove2me | Theorems.Thm_Value_stAppendedZero
-- name    : Value.stAppendedZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:23:08.516023+00:00
-- url     : https://prove2.me/theorems/e5a3ee29-d5cb-4e93-882a-05d666b10bfc
-- title:
--   Value: st Appended Zero
-- statement:
--   «the appended bits must be 0»: otherwise the factor [all appended bits are 0] of one of the
--   tables is 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L62-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L62-L67

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

theorem Value.stAppendedZero : StAppendedZero := by sorry
