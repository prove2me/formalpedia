-- Prove2me | Theorems.Thm_QueryMachines_Tower_selfCallRuns
-- name    : QueryMachines.Tower.selfCallRuns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:04.893665+00:00
-- url     : https://prove2.me/theorems/b102ec13-03fc-49dd-8293-631f1611d27d
-- title:
--   Tower: self Call Runs
-- statement:
--   `selfCall M` returns `val a` within `T a` operations on every good input a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L107-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L107-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Definitions.Def_Tower_Kernel
import Definitions.Def_Tower_Runs
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Q A α β : Type} (M : QueryMachine (Q ⊕ α) (A ⊕ β) α β)

theorem QueryMachines.Tower.selfCallRuns : SelfCallRuns := by sorry
