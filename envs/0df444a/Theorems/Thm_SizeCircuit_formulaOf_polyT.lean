-- Prove2me | Theorems.Thm_SizeCircuit_formulaOf_polyT
-- name    : SizeCircuit.formulaOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:26.596674+00:00
-- url     : https://prove2.me/theorems/e0bb4b86-69c2-4c3d-a22d-e48b846db4b6
-- title:
--   Size Circuit: formula Of poly T
-- statement:
--   The formula of a circuit is polynomial time in (n in binary, the circuit).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/SizedCert.lean#L45-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/SizedCert.lean#L45-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_SizedCert
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight

theorem SizeCircuit.formulaOf_polyT : PolyT fun p : ℕ × List GateD => formulaOf p.1 p.2 := by sorry
