-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_toStepped_reaches
-- name    : QueryMachines.QueryMachine.toStepped_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:14.375363+00:00
-- url     : https://prove2.me/theorems/28b1c802-0eee-40c0-be86-d130271b43e6
-- title:
--   Query Machine: to Stepped reaches
-- statement:
--   A run without queries is a run of the step machine underneath.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L262-L267
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L262-L267

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

theorem QueryMachines.QueryMachine.toStepped_reaches {M : QueryMachine Q A α β} {O : Q → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ} (h : M.Reaches O S b s own L) (hL : L = []) :
    M.toStepped.Reaches S b s own := by sorry
