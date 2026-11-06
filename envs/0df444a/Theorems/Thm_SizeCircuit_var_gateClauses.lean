-- Prove2me | Theorems.Thm_SizeCircuit_var_gateClauses
-- name    : SizeCircuit.var_gateClauses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:30:58.750915+00:00
-- url     : https://prove2.me/theorems/035d94e0-ad6f-4cf7-b307-ed5c4501a32c
-- title:
--   Size Circuit: var gate Clauses
-- statement:
--   The variables of the four clauses of a gate are the two wires that it reads and its own wire.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L35-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L35-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.var_gateClauses {i : ℕ} {g : GateD} {C : List (ℕ × Bool)} (hC : C ∈ gateClauses i g) {l : ℕ × Bool} (hl : l ∈ C) :
    l.1 = g.2.1 ∨ l.1 = g.2.2 ∨ l.1 = i := by sorry
