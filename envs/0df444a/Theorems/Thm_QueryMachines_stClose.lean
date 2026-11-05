-- Prove2me | Theorems.Thm_QueryMachines_stClose
-- name    : QueryMachines.stClose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:20.756186+00:00
-- url     : https://prove2.me/theorems/f2832065-7c3e-49b2-aeaf-2fe6ee969c1e
-- title:
--   Query Machines: st Close
-- statement:
--   `StClose`: cost at one operation per query is the number of steps with the oracle built in.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L288-L290
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L288-L290

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
open QueryMachines
open Groundwork QueryMachine

theorem QueryMachines.stClose : StClose := by sorry
