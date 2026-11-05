-- Prove2me | Theorems.Thm_QueryMachines_stMono
-- name    : QueryMachines.stMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:24.969271+00:00
-- url     : https://prove2.me/theorems/518522e3-0638-4957-ab88-effe2d8fc3c3
-- title:
--   Query Machines: st Mono
-- statement:
--   `StMono`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L276-L276
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L276-L276

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

theorem QueryMachines.stMono : StMono := by sorry
