-- Prove2me | Theorems.Thm_SizeCircuit_wfa_halfAdder
-- name    : SizeCircuit.wfa_halfAdder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:49.044263+00:00
-- url     : https://prove2.me/theorems/b483dc76-ed0c-46c7-bb74-cd72e396d9c3
-- title:
--   Size Circuit: wfa half Adder
-- statement:
--   The gates of a half adder read earlier wires only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L78-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L78-L81

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

theorem SizeCircuit.wfa_halfAdder {N a u : ℕ} (ha : a < N) (hu : u < N) : WFa N (halfAdder a u) := by sorry
