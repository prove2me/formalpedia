-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
-- name    : QueryMachines.QueryMachine.WithinFrom.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:58.507521+00:00
-- url     : https://prove2.me/theorems/67cb55d1-d74d-495d-bc32-49d1d4dc240c
-- title:
--   Within From: mono
-- statement:
--   The cost and the bound on the sizes may be raised (from a state).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L43-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L43-L45

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

theorem QueryMachines.QueryMachine.WithinFrom.mono {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {S S' T T' : ℕ} {b : β} {s : M.σ}
    (h : M.WithinFrom O w s T S b) (hT : T ≤ T') (hS : S ≤ S') : M.WithinFrom O w s T' S' b := by sorry
