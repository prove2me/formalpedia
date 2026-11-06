-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_both_reaches
-- name    : QueryMachines.QueryMachine.both_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:44:15.609192+00:00
-- url     : https://prove2.me/theorems/9e29d980-ce4b-4dd9-a73c-eb8e9d15456c
-- title:
--   Query Machine: both reaches
-- statement:
--   `both`, from a state of the first machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L100-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L100-L127

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

theorem QueryMachines.QueryMachine.both_reaches [HasSize α] [HasSize β] {M : QueryMachine Q A α β} {N : QueryMachine Q A α γ} {O : Q → Option A} {a : α} {t t' S S' : ℕ} {L L' : List Q} {b : β} {c : γ} {s : M.σ}
    (h : M.Reaches O S b s t L) (h' : N.Runs O a t' L' S' c) : (both M N).Reaches O (max (size a + S) (size b + S') + 1) (b, c) (.inl (a, s)) (t + 1 + t') (L ++ L') := by sorry
