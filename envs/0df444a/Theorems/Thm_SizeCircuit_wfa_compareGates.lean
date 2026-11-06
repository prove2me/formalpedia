-- Prove2me | Theorems.Thm_SizeCircuit_wfa_compareGates
-- name    : SizeCircuit.wfa_compareGates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:09.134092+00:00
-- url     : https://prove2.me/theorems/10cd63f3-1469-443f-a55c-5cff1b4dd7a9
-- title:
--   Size Circuit: wfa compare Gates
-- statement:
--   The gates of the comparison read earlier wires only, if there is a wire 0 and the digit wires
--   exist.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L90-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L90-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.wfa_compareGates {N s : ℕ} {digits : List ℕ} (hN : 0 < N) (hd : ∀ x ∈ digits, x < N) : WFa N (compareGates N s digits) := by sorry
