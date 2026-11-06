-- Prove2me | Theorems.Thm_SizeCircuit_holds_gateClauses
-- name    : SizeCircuit.holds_gateClauses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:31.211241+00:00
-- url     : https://prove2.me/theorems/96795676-0ac9-460a-90f0-edc649d2ff93
-- title:
--   Size Circuit: holds gate Clauses
-- statement:
--   The four clauses of a gate hold exactly if the variable of its wire has the value of the gate.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L80-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L80-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.holds_gateClauses (a : ℕ → Bool) (i : ℕ) (g : GateD) : Holds a (gateClauses i g) ↔ a i = gval a g := by sorry
