-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_subst_reaches
-- name    : QueryMachines.QueryMachine.subst_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:59.337671+00:00
-- url     : https://prove2.me/theorems/781b72f7-95fc-4bc3-9395-77b7644f910c
-- title:
--   Query Machine: subst reaches
-- statement:
--   Queries answered by a machine with query access, from a state of the outer machine: own steps
--   add up, with two more for each query; the lists of queries of the answering runs are joined.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L183-L204
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L183-L204

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

theorem QueryMachines.QueryMachine.subst_reaches {O : Q → Option A} {c : C} {s : M.σ} {own S S' : ℕ} {L : List Q} {b : β} {t : Q → ℕ} {L' : Q → List Q'} (h : M.Reaches O S b s own L)
    (hN : ∀ x ∈ L, ∀ v, O x = some v → N.Runs O' (c, x) (t x) (L' x) S' v) :
    (M.subst N).Reaches O' (size c + S + S' + 1) b (c, .inl s) (own + (L.map fun x => t x + 2).sum) (L.flatMap L') := by sorry
