-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_sum_map_const
-- name    : QueryMachines.QueryMachine.sum_map_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:49:09.023199+00:00
-- url     : https://prove2.me/theorems/6d86f083-1389-4c7b-9b7b-1d80c8713e67
-- title:
--   Query Machine: sum map const
-- statement:
--   At t operations per query, the queries of a list cost its length times t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L83-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L83-L86

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

theorem QueryMachines.QueryMachine.sum_map_const (L : List Q) (t : ℕ) : (L.map fun _ => t).sum = L.length * t := by sorry
