-- Prove2me | Theorems.Thm_SizeCircuit_compareGates_polyT
-- name    : SizeCircuit.compareGates_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:57.568756+00:00
-- url     : https://prove2.me/theorems/a8ecad5e-6647-4fe1-b1ae-3e137e1de53e
-- title:
--   Size Circuit: compare Gates poly T
-- statement:
--   The gates of the comparison are polynomial time in (N, s, the list of digit wires).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L158-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L158-L165

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Cert
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.compareGates_polyT : PolyT fun q : ℕ × ℕ × List ℕ => compareGates q.1 q.2.1 q.2.2 := by sorry
