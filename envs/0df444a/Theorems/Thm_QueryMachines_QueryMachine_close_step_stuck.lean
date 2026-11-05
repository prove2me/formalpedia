-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_step_stuck
-- name    : QueryMachines.QueryMachine.close_step_stuck
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:45.807661+00:00
-- url     : https://prove2.me/theorems/1daae87c-0a23-4183-bcac-5ae9bc26f882
-- title:
--   Query Machine: close step stuck
-- statement:
--   With the oracle built in: a state that asks a query without an answer stays where it is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L104-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L104-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}

theorem QueryMachines.QueryMachine.close_step_stuck {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} {x : Q} (h : M.ask s = some x) (hv : O x = none) :
    (M.close O).step s = s := by sorry
