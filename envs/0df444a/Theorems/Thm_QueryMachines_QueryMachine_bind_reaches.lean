-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_bind_reaches
-- name    : QueryMachines.QueryMachine.bind_reaches
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:44:20.777194+00:00
-- url     : https://prove2.me/theorems/351a5de3-7f09-4c50-b326-b636c7293684
-- title:
--   Query Machine: bind reaches
-- statement:
--   `bind`, from a state of the first machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L62-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L62-L89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.bind_reaches [HasSize α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {a : α} {t t' S S' : ℕ} {L L' : List Q} {b : β} {c : γ} {s : M.σ}
    (h : M.Reaches O S b s t L) (h' : N.Runs O (a, b) t' L' S' c) : (bind M N).Reaches O (max (size a + S) S' + 1) c (.inl (a, s)) (t + 1 + t') (L ++ L') := by sorry
