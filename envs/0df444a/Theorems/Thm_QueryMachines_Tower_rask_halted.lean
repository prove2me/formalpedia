-- Prove2me | Theorems.Thm_QueryMachines_Tower_rask_halted
-- name    : QueryMachines.Tower.rask_halted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:48:10.578375+00:00
-- url     : https://prove2.me/theorems/db379278-3f8e-4876-bc5f-1efcb36f1cfe
-- title:
--   Tower: rask halted
-- statement:
--   A halted activation asks nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Runs.lean#L38-L38

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

theorem QueryMachines.Tower.rask_halted {s : M.σ} {b : β} (K : List M.σ) (h : M.out s = some b) : rask M (s :: K) = none := by sorry
