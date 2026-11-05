-- Prove2me | Theorems.Thm_QueryMachines_Tower_wfHalt
-- name    : QueryMachines.Tower.wfHalt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:48.970347+00:00
-- url     : https://prove2.me/theorems/273979f6-b5a7-4127-bca5-e39828880360
-- title:
--   Tower: wf Halt
-- statement:
--   A halted state costs nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean#L28-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean#L28-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_Tower_Kernel
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
open Groundwork
variable {Q A α β : Type} {M : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {s : M.σ} {b : β} {S S' T T' : ℕ}

theorem QueryMachines.Tower.wfHalt (h1 : M.out s = some b) (h2 : size s ≤ S) : M.WithinFrom O w s T S b := by sorry
