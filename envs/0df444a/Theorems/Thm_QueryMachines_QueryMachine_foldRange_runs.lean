-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_foldRange_runs
-- name    : QueryMachines.QueryMachine.foldRange_runs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:46:12.52852+00:00
-- url     : https://prove2.me/theorems/df2db554-6fe1-429c-b68b-d5351b792000
-- title:
--   Query Machine: fold Range runs
-- statement:
--   The loop over a range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L216-L241
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L216-L241

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_Stepped_foldRange_runs
attribute [local fun_prop] Groundwork.PolyT.flatMap


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.foldRange_runs [HasSize α] [HasSize γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} {O : Q → Option A} {a : α}
    (t : ℕ → ℕ) (Lq : ℕ → List Q) (v : ℕ → β) (Sc Sm : ℕ) (hM : ∀ y < N a, M.Runs O (a, y) (t y) (Lq y) Sm (v y))
    (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (foldRange N M g c₀).Runs O a (∑ y ∈ range (N a), (t y + 1)) ((List.range (N a)).flatMap Lq) (size a + size (N a) + (Sc + Sm) + 1)
      ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by sorry
