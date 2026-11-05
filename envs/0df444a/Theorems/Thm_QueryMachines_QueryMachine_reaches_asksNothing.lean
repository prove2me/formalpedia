-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_reaches_asksNothing
-- name    : QueryMachines.QueryMachine.reaches_asksNothing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:52:13.021433+00:00
-- url     : https://prove2.me/theorems/7e11fe40-493e-43ac-be9e-7d33cb9217a5
-- title:
--   Query Machine: reaches asks Nothing
-- statement:
--   A step machine, seen as a machine that asks nothing, runs as it did.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L255-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L255-L259

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

theorem QueryMachines.QueryMachine.reaches_asksNothing {R : Stepped α β} {O : Q → Option A} {S t : ℕ} {b : β} {s : R.σ} (h : R.Reaches S b s t) :
    ({ R with ask := fun _ => none, resume := fun s _ => s } : QueryMachine Q A α β).Reaches O S b s t [] := by sorry
