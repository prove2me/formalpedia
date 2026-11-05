-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_close_reaches
-- name    : QueryMachines.QueryMachine.close_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:56.796588+00:00
-- url     : https://prove2.me/theorems/60b4ef7e-db4b-40bb-a4a9-919d5cd7707e
-- title:
--   Query Machine: close reaches
-- statement:
--   A run with query access is a run of the machine with the oracle built in; each query is one
--   step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L134-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L134-L143

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

theorem QueryMachines.QueryMachine.close_reaches {M : QueryMachine Q A α β} {O : Q → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (h : M.Reaches O S b s own L) : (M.close O).Reaches S b s (own + L.length) := by sorry
