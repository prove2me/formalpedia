-- Prove2me | Theorems.Thm_QueryMachines_QueryMachine_orbit_range
-- name    : QueryMachines.QueryMachine.orbit_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:45:06.424773+00:00
-- url     : https://prove2.me/theorems/e44f7eab-71d9-46bc-96ec-1ce35a77ecd8
-- title:
--   Query Machine: orbit range
-- statement:
--   The points of the loop over y < N a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L201-L207
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/QueryMachines/CombRuns.lean#L201-L207

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Stepped_orbit_range
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.QueryMachine
open Groundwork Finset
variable {Q Q' A α α₁ α₂ β γ τ : Type}

theorem QueryMachines.QueryMachine.orbit_range (N : α → ℕ) (a : α) (k y : ℕ) (h : y + k = N a) :
    Stepped.Orbit (Stepped.rangeNext N) (if y < N a then some (a, y) else none) ((List.range' y k).map fun y => (a, y)) := by sorry
