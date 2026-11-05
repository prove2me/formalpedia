-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_foldWhile_body
-- name    : QueryMachines.QueryMachine.foldWhile_body
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:45:37.562475+00:00
-- url     : https://prove2.me/theorems/ba358280-88ce-406c-88b9-bb528c29d5ae
-- title:
--   Query Machine: fold While body
-- statement:
--   The body, run inside the loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L150-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L150-L178

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_Stepped_foldWhile_body

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : QueryMachine Q A τ β} {g : γ → τ → β → γ} {c₀ : α → γ} {O : Q → Option A}

theorem QueryMachines.QueryMachine.foldWhile_body {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} {L L' : List Q} (h : M.Reaches O Sm b s t L) (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldWhile start nxt M g c₀).Reaches O S r (Stepped.foldGo M.toStepped (g c x b) (nxt x)) T L') :
    (foldWhile start nxt M g c₀).Reaches O S r (.inl (x, c, s)) (t + 1 + T) (L ++ L') := by sorry
