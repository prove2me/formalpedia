-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_mapAsk_reaches
-- name    : QueryMachines.QueryMachine.mapAsk_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:43:47.187225+00:00
-- url     : https://prove2.me/theorems/7f1b2233-454a-4be7-be42-125dd3bd210a
-- title:
--   Query Machine: map Ask reaches
-- statement:
--   Queries rewritten by h (from a state).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L30-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L30-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.mapAsk_reaches {h : Q → Q'} {M : QueryMachine Q A α β} {O : Q' → Option A} {S own : ℕ} {L : List Q} {b : β} {s : M.σ}
    (hr : M.Reaches (fun x => O (h x)) S b s own L) : (mapAsk h M).Reaches O S b s own (L.map h) := by sorry
