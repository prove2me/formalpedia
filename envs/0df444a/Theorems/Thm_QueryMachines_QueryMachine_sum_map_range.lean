-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_sum_map_range
-- name    : QueryMachines.QueryMachine.sum_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:45:18.420419+00:00
-- url     : https://prove2.me/theorems/3523b636-bbc6-44d8-84d4-4413707f7498
-- title:
--   Query Machine: sum map range
-- statement:
--   A sum over a list of numbers 0, …, n − 1 as a sum over a range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L210-L213
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L210-L213

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Stepped_sum_map_range
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.sum_map_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ y ∈ range n, f y := by sorry
