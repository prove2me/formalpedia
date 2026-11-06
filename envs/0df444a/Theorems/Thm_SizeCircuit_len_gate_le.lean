-- Prove2me | Theorems.Thm_SizeCircuit_len_gate_le
-- name    : SizeCircuit.len_gate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:40.381906+00:00
-- url     : https://prove2.me/theorems/154e9ef9-7ca1-451e-a135-ed6468557274
-- title:
--   Size Circuit: len gate le
-- statement:
--   The word of a gate that names wires up to M has length at most 6M + 18.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L88-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L88-L94

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

theorem SizeCircuit.len_gate_le (g : GateD) {M : ℕ} (h1 : g.2.1 ≤ M) (h2 : g.2.2 ≤ M) : len g ≤ 6 * M + 18 := by sorry
