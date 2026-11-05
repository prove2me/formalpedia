-- Prove2me | Theorems.Thm_QueryMachines_Tower_wfStep
-- name    : QueryMachines.Tower.wfStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:33.102467+00:00
-- url     : https://prove2.me/theorems/7c43a402-d3fc-49a2-9df6-6575216906b1
-- title:
--   Tower: wf Step
-- statement:
--   An own step costs 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean#L31-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean#L31-L32

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

theorem QueryMachines.Tower.wfStep (h1 : M.out s = none) (h2 : M.ask s = none) (h3 : size s ≤ S) (h : M.WithinFrom O w (M.step s) T S b) : M.WithinFrom O w s (T + 1) S b := by sorry
