-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_sum_map_unitCost
-- name    : QueryMachines.QueryMachine.sum_map_unitCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:41.99399+00:00
-- url     : https://prove2.me/theorems/b3a977c6-335b-4660-a7da-77693f91053d
-- title:
--   Query Machine: sum map unit Cost
-- statement:
--   At one operation per query, the queries of a list cost its length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L77-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L77-L80

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

theorem QueryMachines.QueryMachine.sum_map_unitCost (L : List Q) : (L.map unitCost).sum = L.length := by sorry
