-- Prove2me | Theorems.Thm_QueryMachines_Tower_rstep_call
-- name    : QueryMachines.Tower.rstep_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:49:30.645196+00:00
-- url     : https://prove2.me/theorems/6015a756-4791-4892-8390-198132fe91b8
-- title:
--   Tower: rstep call
-- statement:
--   A call starts a new activation on top.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L53-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L53-L53

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

theorem QueryMachines.Tower.rstep_call {s : M.σ} {a' : α} (K : List M.σ) (h1 : M.out s = none) (h2 : M.ask s = some (Sum.inr a')) : rstep M (s :: K) = M.init a' :: s :: K := by sorry
