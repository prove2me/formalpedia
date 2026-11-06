-- Prove2me | Theorems.Thm_SizeCircuit_addValue_added
-- name    : SizeCircuit.addValue_added
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:37.051984+00:00
-- url     : https://prove2.me/theorems/e2842daf-7cca-4e84-a6c7-ba6c1b7596d3
-- title:
--   Size Circuit: add Value added
-- statement:
--   **At the end the digits write the number of inputs that are 1**, under all values v of the wires
--   that obey the gates of the addition.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L270-L275
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L270-L275

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.addValue_added (v : ℕ → Bool) (n : ℕ) (h : Obeys v n (added n).2.2.2) : ofWord ((added n).2.2.1.map v) = onesAmong v (List.range n) := by sorry
