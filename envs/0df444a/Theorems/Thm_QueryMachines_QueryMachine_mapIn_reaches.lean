-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_mapIn_reaches
-- name    : QueryMachines.QueryMachine.mapIn_reaches
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:44:27.710196+00:00
-- url     : https://prove2.me/theorems/7edb72d2-ae94-4e17-9413-469fd722920d
-- title:
--   Query Machine: map In reaches
-- statement:
--   A function applied to the input (from a state).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L38-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L38-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_Stepped_mapIn_reaches

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.mapIn_reaches {g : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {S own : ℕ} {L : List Q} {c : γ} {s : M.σ}
    (hr : M.Reaches O S c s own L) : (mapIn g M).Reaches O S c s own L := by sorry
