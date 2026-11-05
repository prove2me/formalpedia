-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_mapIn
-- name    : QueryMachines.QueryMachine.close_mapIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:14:26.213487+00:00
-- url     : https://prove2.me/theorems/ac741377-facf-43ef-840c-5484defa7fd4
-- title:
--   Query Machine: close map In
-- statement:
--   `close` commutes with `mapIn`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L56-L57

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

theorem QueryMachines.QueryMachine.close_mapIn (g : α → β) (M : QueryMachine Q A β γ) (O : Q → Option A) :
    (mapIn g M).close O = Stepped.mapIn g (M.close O) := by sorry

attribute [defeq] QueryMachines.QueryMachine.close_mapIn
