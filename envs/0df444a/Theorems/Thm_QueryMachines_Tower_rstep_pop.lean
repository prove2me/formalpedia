-- Prove2me | Theorems.Thm_QueryMachines_Tower_rstep_pop
-- name    : QueryMachines.Tower.rstep_pop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:48:21.496407+00:00
-- url     : https://prove2.me/theorems/6c4c3167-61a7-485a-a362-d839070384b2
-- title:
--   Tower: rstep pop
-- statement:
--   The result of a halted activation goes to the one below it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L56-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L56-L56

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

theorem QueryMachines.Tower.rstep_pop {s s' : M.σ} {b : β} (K : List M.σ) (h : M.out s = some b) : rstep M (s :: s' :: K) = M.resume s' (Sum.inr b) :: K := by sorry
