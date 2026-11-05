-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_step_none
-- name    : QueryMachines.QueryMachine.close_step_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:36.211089+00:00
-- url     : https://prove2.me/theorems/ee8b5dc2-ac39-40fc-ad12-1603ecadb23d
-- title:
--   Query Machine: close step none
-- statement:
--   With the oracle built in: a state that asks nothing makes its own step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L91-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L91-L93

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

theorem QueryMachines.QueryMachine.close_step_none {M : QueryMachine Q A α β} {O : Q → Option A} {s : M.σ} (h : M.ask s = none) : (M.close O).step s = M.step s := by sorry
