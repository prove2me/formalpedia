-- Prove2me | Theorems.Thm_SizeCircuit_le_numVars
-- name    : SizeCircuit.le_numVars
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:50:44.864195+00:00
-- url     : https://prove2.me/theorems/8bcaa7e9-9761-4a1b-b89e-9d307982617e
-- title:
--   Size Circuit: le num Vars
-- statement:
--   Γ has the variables x₀ … xₙ₋₁ among its variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Sized.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Sized.lean#L35-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_SizeCircuit_Gamma
import Definitions.Def_GraphProblems_Sized
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Sized
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight

theorem SizeCircuit.le_numVars (gates : ℕ → ℕ → List GateD) (n s : ℕ) : n ≤ numVars gates n s := by sorry
