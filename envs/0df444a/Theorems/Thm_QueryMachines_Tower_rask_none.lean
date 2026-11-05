-- Prove2me | Theorems.Thm_QueryMachines_Tower_rask_none
-- name    : QueryMachines.Tower.rask_none
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:50:24.336768+00:00
-- url     : https://prove2.me/theorems/5e4b48e6-19df-4a8a-961e-9f00ca9aa628
-- title:
--   Tower: rask none
-- statement:
--   An activation that asks nothing: the whole asks nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L41-L41

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

theorem QueryMachines.Tower.rask_none {s : M.σ} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = none) : rask M (s :: K) = none := by sorry
