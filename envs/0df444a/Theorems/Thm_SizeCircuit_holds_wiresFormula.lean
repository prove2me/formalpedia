-- Prove2me | Theorems.Thm_SizeCircuit_holds_wiresFormula
-- name    : SizeCircuit.holds_wiresFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:18.219122+00:00
-- url     : https://prove2.me/theorems/d8f60a99-f2dd-4231-9f9e-fae938247e69
-- title:
--   Size Circuit: holds wires Formula
-- statement:
--   The clauses of all gates hold under a exactly if, under a, the variable of every gate has the
--   value of the gate.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L100-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L100-L101

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

theorem SizeCircuit.holds_wiresFormula (a : ℕ → Bool) (n : ℕ) (K : List GateD) : Holds a (wiresFormula n K) ↔ Obeys a n K := by sorry
