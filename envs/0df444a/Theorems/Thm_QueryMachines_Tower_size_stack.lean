-- Prove2me | Theorems.Thm_QueryMachines_Tower_size_stack
-- name    : QueryMachines.Tower.size_stack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:23.33278+00:00
-- url     : https://prove2.me/theorems/f149a7b6-8874-4477-95a8-9be96589904e
-- title:
--   Tower: size stack
-- statement:
--   The size of a stack.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L59-L60

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

theorem QueryMachines.Tower.size_stack (s : M.σ) (K : List M.σ) : size (s :: K) = size s + 1 + size K := by sorry
