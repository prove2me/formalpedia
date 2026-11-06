-- Prove2me | Theorems.Thm_SizeCircuit_wfa_fullAdder
-- name    : SizeCircuit.wfa_fullAdder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:55.423208+00:00
-- url     : https://prove2.me/theorems/7936679c-9506-40dc-a221-846987d3f566
-- title:
--   Size Circuit: wfa full Adder
-- statement:
--   The gates of a full adder read earlier wires only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L72-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L72-L75

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

theorem SizeCircuit.wfa_fullAdder {N a u w : ℕ} (ha : a < N) (hu : u < N) (hw : w < N) : WFa N (fullAdder N a u w) := by sorry
