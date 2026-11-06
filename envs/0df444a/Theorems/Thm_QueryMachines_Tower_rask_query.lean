-- Prove2me | Theorems.Thm_QueryMachines_Tower_rask_query
-- name    : QueryMachines.Tower.rask_query
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:48:45.010715+00:00
-- url     : https://prove2.me/theorems/15541925-4b54-4c52-becc-6369e9172a18
-- title:
--   Tower: rask query
-- statement:
--   A query that is not a call is the query of the whole.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L47-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L47-L47

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

theorem QueryMachines.Tower.rask_query {s : M.σ} {x : Q} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = some (Sum.inl x)) : rask M (s :: K) = some x := by sorry
