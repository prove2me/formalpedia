-- Prove2me | Theorems.Thm_QueryMachines_Tower_rask_call
-- name    : QueryMachines.Tower.rask_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:47:45.254641+00:00
-- url     : https://prove2.me/theorems/3ccb00fc-d678-4632-a3cf-37396fce57a0
-- title:
--   Tower: rask call
-- statement:
--   A call is not a query of the whole.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L44-L44

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

theorem QueryMachines.Tower.rask_call {s : M.σ} {a' : α} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = some (Sum.inr a')) : rask M (s :: K) = none := by sorry
