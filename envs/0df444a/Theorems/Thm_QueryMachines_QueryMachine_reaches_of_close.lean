-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_reaches_of_close
-- name    : QueryMachines.QueryMachine.reaches_of_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:56.859203+00:00
-- url     : https://prove2.me/theorems/73dab7f7-31f2-450e-a8d2-77e73ede19bb
-- title:
--   Query Machine: reaches of close
-- statement:
--   A run of the machine with the oracle built in is a run with query access; its steps are the own
--   steps and the queries.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L113-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L113-L130

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

theorem QueryMachines.QueryMachine.reaches_of_close {M : QueryMachine Q A α β} {O : Q → Option A} {S T : ℕ} {b : β} {s : (M.close O).σ}
    (h : (M.close O).Reaches S b s T) : ∃ (own : ℕ) (L : List Q), M.Reaches O S b s own L ∧ own + L.length ≤ T := by sorry
