-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_const
-- name    : QueryMachines.QueryMachine.close_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:16:48.606328+00:00
-- url     : https://prove2.me/theorems/debe50d1-bfc4-4e88-a02a-df1d1ba95a62
-- title:
--   Query Machine: close const
-- statement:
--   A constant stays what it is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L119-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L119-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Comb
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}

theorem QueryMachines.QueryMachine.close_const [HasSize α] [HasSize β] (b : β) (O : Q → Option A) :
    (const b : QueryMachine Q A α β).close O = Stepped.const b := by sorry

attribute [defeq] QueryMachines.QueryMachine.close_const
