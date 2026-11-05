-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_subst_reaches_within
-- name    : QueryMachines.QueryMachine.subst_reaches_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:54.83554+00:00
-- url     : https://prove2.me/theorems/2c9051b7-c516-4a72-979d-306616377456
-- title:
--   Query Machine: subst reaches within
-- statement:
--   The same in costs: if the answer to x costs at most t x at the prices w', the whole costs at
--   most own + Σ (t x + 2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L208-L227
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L208-L227

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Tactic
import Definitions.Def_QueryMachines_Runs
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork
variable {Q A Q' A' C α β : Type}
variable [HasSize C] {M : QueryMachine Q A α β} {N : QueryMachine Q' A' (C × Q) A} {O' : Q' → Option A'}

theorem QueryMachines.QueryMachine.subst_reaches_within {O : Q → Option A} {w' : Q' → ℕ} {c : C} {s : M.σ} {own S S' : ℕ} {L : List Q} {b : β} {t : Q → ℕ} (h : M.Reaches O S b s own L)
    (hN : ∀ x v, O x = some v → N.Within O' w' (c, x) (t x) S' v) :
    ∃ (own₂ : ℕ) (L₂ : List Q'), (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) own₂ L₂ ∧ own₂ + (L₂.map w').sum ≤ own + (L.map fun x => t x + 2).sum := by sorry
