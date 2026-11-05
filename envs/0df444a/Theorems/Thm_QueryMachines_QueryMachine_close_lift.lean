-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_lift
-- name    : QueryMachines.QueryMachine.close_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:17:45.994846+00:00
-- url     : https://prove2.me/theorems/185e5702-f937-4970-b90d-06b101313886
-- title:
--   Query Machine: close lift
-- statement:
--   A step machine stays what it is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Comb.lean#L41-L41

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

theorem QueryMachines.QueryMachine.close_lift (M : Stepped α β) (O : Q → Option A) : (lift M : QueryMachine Q A α β).close O = M := by sorry

attribute [defeq] QueryMachines.QueryMachine.close_lift
