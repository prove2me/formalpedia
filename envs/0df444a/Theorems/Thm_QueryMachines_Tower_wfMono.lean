-- Prove2me | Theorems.Thm_QueryMachines_Tower_wfMono
-- name    : QueryMachines.Tower.wfMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:52.772597+00:00
-- url     : https://prove2.me/theorems/47bb5f6f-db26-4d80-8e7f-1f240cf61d45
-- title:
--   Tower: wf Mono
-- statement:
--   The cost and the bound on the sizes may be raised.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean#L25-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean#L25-L25

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

theorem QueryMachines.Tower.wfMono (h : M.WithinFrom O w s T S b) (hT : T ≤ T') (hS : S ≤ S') : M.WithinFrom O w s T' S' b := by sorry
