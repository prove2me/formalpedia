-- Prove2me | Theorems.Thm_SizeCircuit_added_spec
-- name    : SizeCircuit.added_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:51:45.31814+00:00
-- url     : https://prove2.me/theorems/4e5a8398-ead5-4cc6-a279-0083fb061b6a
-- title:
--   Size Circuit: added spec
-- statement:
--   **After the n steps**: no wire waits; all digit wires exist; the gates read earlier wires only;
--   there are at most 5n gates and at most n digits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L198-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L198-L201

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

theorem SizeCircuit.added_spec (n : ℕ) : (added n).1 = [] ∧ (added n).2.1 = [] ∧ (∀ x ∈ (added n).2.2.1, x < n + (added n).2.2.2.length) ∧ WFa n (added n).2.2.2 ∧
    (added n).2.2.2.length ≤ 5 * n ∧ (added n).2.2.1.length ≤ n := by sorry
