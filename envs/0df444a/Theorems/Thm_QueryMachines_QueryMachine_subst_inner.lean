-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_subst_inner
-- name    : QueryMachines.QueryMachine.subst_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:58.709238+00:00
-- url     : https://prove2.me/theorems/ec1e3897-d332-4ed5-b369-5f451f76d1c7
-- title:
--   Query Machine: subst inner
-- statement:
--   The answering machine, run inside.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L152-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/Runs.lean#L152-L179

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

theorem QueryMachines.QueryMachine.subst_inner {c : C} {m : M.σ} {r : N.σ} {v : A} {b : β} {t T S' Sg : ℕ} {L₁ L₂ : List Q'} (h : N.Reaches O' S' v r t L₁) (hm : size c + (size m + S' + 1) ≤ Sg)
    (hT : (M.subst N).Reaches O' Sg b (c, .inl (M.resume m v)) T L₂) : (M.subst N).Reaches O' Sg b (c, .inr (m, r)) (t + 1 + T) (L₁ ++ L₂) := by sorry
