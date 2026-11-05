-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_step_some
-- name    : QueryMachines.QueryMachine.close_step_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:54.385463+00:00
-- url     : https://prove2.me/theorems/9874c9a6-9fa1-41ea-8dd7-ee2899b91cbe
-- title:
--   Query Machine: close step some
-- statement:
--   With the oracle built in: a state that asks x goes on with the answer to x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L96-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L96-L101

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

theorem QueryMachines.QueryMachine.close_step_some {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} {x : Q} {v : A} (h : M.ask s = some x) (hv : O x = some v) :
    (M.close O).step s = M.resume s v := by sorry
