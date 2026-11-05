-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_mapOut
-- name    : QueryMachines.QueryMachine.close_mapOut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:14:44.560336+00:00
-- url     : https://prove2.me/theorems/81ff8eed-4b64-46da-98fe-ab60016275e9
-- title:
--   Query Machine: close map Out
-- statement:
--   `close` commutes with `mapOut`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L60-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_QueryMachines_Comb
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' C α α₁ α₂ β γ δ ι τ : Type}

theorem QueryMachines.QueryMachine.close_mapOut (M : QueryMachine Q A α β) (g : β → γ) (O : Q → Option A) :
    (mapOut M g).close O = Stepped.mapOut (M.close O) g := by sorry

attribute [defeq] QueryMachines.QueryMachine.close_mapOut
