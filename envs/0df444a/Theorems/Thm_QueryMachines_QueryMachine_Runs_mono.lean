-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
-- name    : QueryMachines.QueryMachine.Runs.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:59.033373+00:00
-- url     : https://prove2.me/theorems/98b77c6e-884b-4a74-9ab4-baf61a0c8c7e
-- title:
--   Runs: mono
-- statement:
--   The same for runs from the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L39-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L39-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}

theorem QueryMachines.QueryMachine.Runs.mono {M : QueryMachine Q A α β} {O : Q → Option A} {S S' own own' : ℕ} {L : List Q} {b : β} {a : α}
    (h : M.Runs O a own L S b) (ho : own ≤ own') (hS : S ≤ S') : M.Runs O a own' L S' b := by sorry
