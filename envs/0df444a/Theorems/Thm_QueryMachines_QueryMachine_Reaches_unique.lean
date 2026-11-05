-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_Reaches_unique
-- name    : QueryMachines.QueryMachine.Reaches.unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:55.764314+00:00
-- url     : https://prove2.me/theorems/447aa5b3-ae8c-427a-b657-1eb715a7e10d
-- title:
--   Reaches: unique
-- statement:
--   From one state and with one oracle, the result and the list of the queries are determined.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L53-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L53-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_Groundwork_Stepped_Runs_unique

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}

theorem QueryMachines.QueryMachine.Reaches.unique {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L L' : List Q} {b b' : β} {s : M.σ}
    (h : M.Reaches O S b s own L) (h' : M.Reaches O S' b' s own' L') : b = b' ∧ L = L' := by sorry
