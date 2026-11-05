-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_foldWhile_reaches
-- name    : QueryMachines.QueryMachine.foldWhile_reaches
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:31:27.180196+00:00
-- url     : https://prove2.me/theorems/3758ea36-1a74-43cb-90c6-5ace97cfa00e
-- title:
--   Query Machine: fold While reaches
-- statement:
--   The loop, from the state with accumulator c and next point o.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L181-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L181-L196

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Stepped_foldWhile_reaches
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : QueryMachine Q A τ β} {g : γ → τ → β → γ} {c₀ : α → γ} {O : Q → Option A}

theorem QueryMachines.QueryMachine.foldWhile_reaches {xs : List τ} {o : Option τ} (ho : Stepped.Orbit nxt o xs) (t : τ → ℕ) (Lq : τ → List Q) (v : τ → β) (Sx Sc Sm : ℕ) (c : γ)
    (hM : ∀ x ∈ xs, M.Runs O x (t x) (Lq x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx) (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldWhile start nxt M g c₀).Reaches O (Sx + (Sc + Sm) + 1) (xs.foldl (fun c x => g c x (v x)) c) (Stepped.foldGo M.toStepped c o) (xs.map fun x => t x + 1).sum (xs.flatMap Lq) := by sorry
