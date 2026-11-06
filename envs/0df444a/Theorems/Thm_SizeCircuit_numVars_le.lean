-- Prove2me | Theorems.Thm_SizeCircuit_numVars_le
-- name    : SizeCircuit.numVars_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:51:25.655347+00:00
-- url     : https://prove2.me/theorems/0e2a0ce5-cf16-4e93-8b08-8f9be6e4bdd4
-- title:
--   Size Circuit: num Vars le
-- statement:
--   Γ has at most (a+1)·(n+1) variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Sized.lean#L40-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Sized.lean#L40-L44

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

theorem SizeCircuit.numVars_le {gates : ℕ → ℕ → List GateD} {a : ℕ} (hT : TestsSize gates a) (n s : ℕ) : numVars gates n s ≤ (a + 1) * (n + 1) := by sorry
