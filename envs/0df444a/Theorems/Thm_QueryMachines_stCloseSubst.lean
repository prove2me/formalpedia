-- Prove2me | Theorems.Thm_QueryMachines_stCloseSubst
-- name    : QueryMachines.stCloseSubst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:05.253587+00:00
-- url     : https://prove2.me/theorems/00c93c84-7fbf-4491-9544-1a15ba1d5f30
-- title:
--   Query Machines: st Close Subst
-- statement:
--   `StCloseSubst`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L320-L320
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L320-L320

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

theorem QueryMachines.stCloseSubst : StCloseSubst := by sorry
