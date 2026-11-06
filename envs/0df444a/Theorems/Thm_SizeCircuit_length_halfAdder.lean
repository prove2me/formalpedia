-- Prove2me | Theorems.Thm_SizeCircuit_length_halfAdder
-- name    : SizeCircuit.length_halfAdder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:49:12.520733+00:00
-- url     : https://prove2.me/theorems/829cc17b-4771-44e3-b132-b419c27b32bd
-- title:
--   Size Circuit: length half Adder
-- statement:
--   A half adder has 2 gates.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L87-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L87-L87

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

theorem SizeCircuit.length_halfAdder (a u : ℕ) : (halfAdder a u).length = 2 := by sorry
