-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_mapOut_reaches
-- name    : QueryMachines.QueryMachine.mapOut_reaches
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:43:59.154233+00:00
-- url     : https://prove2.me/theorems/96545e7d-a951-4593-99c4-183c678565e9
-- title:
--   Query Machine: map Out reaches
-- statement:
--   A function applied to the result (from a state).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L46-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L46-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_Stepped_mapOut_reaches

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.mapOut_reaches {M : QueryMachine Q A α β} {g : β → γ} {O : Q → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches O S b s own L) : (mapOut M g).Reaches O S (g b) s own L := by sorry
