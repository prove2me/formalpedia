-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_both
-- name    : QueryMachines.QueryMachine.close_both
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:15:13.112541+00:00
-- url     : https://prove2.me/theorems/12c10c65-a71c-4141-9b2c-05f3cd45ec1b
-- title:
--   Query Machine: close both
-- statement:
--   `close` commutes with `both`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L102-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L102-L112

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

theorem QueryMachines.QueryMachine.close_both [HasSize α] [HasSize β] (M : QueryMachine Q A α β) (N : QueryMachine Q A α γ) (O : Q → Option A) :
    (both M N).close O = Stepped.both (M.close O) (N.close O) := by sorry
