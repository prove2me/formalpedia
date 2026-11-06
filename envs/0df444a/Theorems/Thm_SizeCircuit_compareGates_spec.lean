-- Prove2me | Theorems.Thm_SizeCircuit_compareGates_spec
-- name    : SizeCircuit.compareGates_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:25.205464+00:00
-- url     : https://prove2.me/theorems/9f498901-dee4-48fe-b0b4-b423accab12f
-- title:
--   Size Circuit: compare Gates spec
-- statement:
--   **The comparison.** Under values v of the wires that obey the gates of the comparison, its last
--   wire is 1 exactly if the digit wires write the number s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L70-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L70-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.compareGates_spec (v : ℕ → Bool) (N s : ℕ) (digits : List ℕ) (h : Obeys v N (compareGates N s digits)) :
    v (N + digits.length) = decide (ofWord (digits.map v) = s) := by sorry
