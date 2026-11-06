-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_bind_reaches_inr
-- name    : QueryMachines.QueryMachine.bind_reaches_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:43:21.041636+00:00
-- url     : https://prove2.me/theorems/409bf14d-9985-441e-a587-ee7caf5add3f
-- title:
--   Query Machine: bind reaches inr
-- statement:
--   The second machine of `bind`, run inside.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L54-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L54-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_Stepped_bind_reaches_inr

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.bind_reaches_inr [HasSize α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {S t : ℕ} {L : List Q} {c : γ} {s : N.σ}
    (h : N.Reaches O S c s t L) : (bind M N).Reaches O (S + 1) c (.inr s) t L := by sorry
