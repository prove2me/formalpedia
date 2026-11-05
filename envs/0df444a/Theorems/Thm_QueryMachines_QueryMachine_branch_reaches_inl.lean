-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_branch_reaches_inl
-- name    : QueryMachines.QueryMachine.branch_reaches_inl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:44:43.60928+00:00
-- url     : https://prove2.me/theorems/57179224-7c89-47c9-8642-bfe7bd632e1e
-- title:
--   Query Machine: branch reaches inl
-- statement:
--   The left machine of `branch`, run inside.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L130-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L130-L135

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_Stepped_branch_reaches_inl

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.branch_reaches_inl {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {s : M₁.σ}
    (h : M₁.Reaches O S b s t L) : (branch sel M₁ M₂).Reaches O (S + 1) b (.inl s) t L := by sorry
