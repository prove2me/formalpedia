-- Prove2me | Theorems.Thm_SizeCircuit_fullAdder_spec
-- name    : SizeCircuit.fullAdder_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:59.393585+00:00
-- url     : https://prove2.me/theorems/bc7d6c5f-ce80-4c15-846f-42b57b29809d
-- title:
--   Size Circuit: full Adder spec
-- statement:
--   The sum and twice the carry of a full adder make the number of ones among its three inputs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L50-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L50-L59

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

theorem SizeCircuit.fullAdder_spec (v : ℕ → Bool) (N a u w : ℕ) (h : Obeys v N (fullAdder N a u w)) :
    (v (N + 1)).toNat + 2 * (v (N + 4)).toNat = (v a).toNat + (v u).toNat + (v w).toNat := by sorry
