-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_branch_reaches_inr
-- name    : QueryMachines.QueryMachine.branch_reaches_inr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:45:23.250347+00:00
-- url     : https://prove2.me/theorems/e0e816b6-2f64-4c8c-925c-bbc9d4db5a69
-- title:
--   Query Machine: branch reaches inr
-- statement:
--   The right machine of `branch`, run inside.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L138-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L138-L143

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_Stepped_branch_reaches_inr

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.branch_reaches_inr {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {S t : ℕ} {L : List Q} {b : β} {s : M₂.σ}
    (h : M₂.Reaches O S b s t L) : (branch sel M₁ M₂).Reaches O (S + 1) b (.inr s) t L := by sorry
