-- Prove2me | Theorems.Thm_QueryMachines_Tower_wfQuery
-- name    : QueryMachines.Tower.wfQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:51.475793+00:00
-- url     : https://prove2.me/theorems/3b1ed2e0-a762-4b5a-b47c-60bb29f0e39f
-- title:
--   Tower: wf Query
-- statement:
--   The query x costs w x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Kernel.lean#L35-L37

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

theorem QueryMachines.Tower.wfQuery {x : Q} {v : A} (h1 : M.out s = none) (h2 : M.ask s = some x) (h3 : O x = some v) (h4 : size s ≤ S) (h : M.WithinFrom O w (M.resume s v) T S b) :
    M.WithinFrom O w s (T + w x) S b := by sorry
