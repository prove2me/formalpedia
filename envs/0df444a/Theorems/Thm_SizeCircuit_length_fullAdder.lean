-- Prove2me | Theorems.Thm_SizeCircuit_length_fullAdder
-- name    : SizeCircuit.length_fullAdder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:47:22.079222+00:00
-- url     : https://prove2.me/theorems/298aa795-028d-443b-87dd-fe52ec21f9a4
-- title:
--   Size Circuit: length full Adder
-- statement:
--   A full adder has 5 gates.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L84-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L84-L84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.length_fullAdder (N a u w : ℕ) : (fullAdder N a u w).length = 5 := by sorry
