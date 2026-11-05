-- Prove2me | Theorems.Thm_QueryMachines_stLiftRuns
-- name    : QueryMachines.stLiftRuns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:22:51.211953+00:00
-- url     : https://prove2.me/theorems/4e2b82f6-4a28-4113-a841-040f22f133af
-- title:
--   Query Machines: st Lift Runs
-- statement:
--   `StLiftRuns`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L250-L250
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L250-L250

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
set_option autoImplicit false
section
section
open QueryMachines
open Groundwork Finset QueryMachine

theorem QueryMachines.stLiftRuns : StLiftRuns := by sorry
