-- Prove2me | Theorems.Thm_SizeCircuit_halfAdder_spec
-- name    : SizeCircuit.halfAdder_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:41.296808+00:00
-- url     : https://prove2.me/theorems/12b33d3f-863d-4d08-b391-66608b1d5741
-- title:
--   Size Circuit: half Adder spec
-- statement:
--   The sum and twice the carry of a half adder make the number of ones among its two inputs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L62-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L62-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.halfAdder_spec (v : ℕ → Bool) (N a u : ℕ) (h : Obeys v N (halfAdder a u)) :
    (v N).toNat + 2 * (v (N + 1)).toNat = (v a).toNat + (v u).toNat := by sorry
