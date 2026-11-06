-- Prove2me | Theorems.Thm_SizeCircuit_iterate_spec
-- name    : SizeCircuit.iterate_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:51:47.081424+00:00
-- url     : https://prove2.me/theorems/64cc34d2-1094-4902-89e6-0f7286a6f580
-- title:
--   Size Circuit: iterate spec
-- statement:
--   After k ≤ n steps: the state is good, n − k wires wait, at most 5k gates are written and at most
--   k digits found.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L181-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L181-L194

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

theorem SizeCircuit.iterate_spec (n : ℕ) : ∀ k ≤ n, AddGood n ((addStep n)^[k] (addStart n)) ∧
    ((addStep n)^[k] (addStart n)).1.length + ((addStep n)^[k] (addStart n)).2.1.length + k = n ∧
    ((addStep n)^[k] (addStart n)).2.2.2.length ≤ 5 * k ∧ ((addStep n)^[k] (addStart n)).2.2.1.length ≤ k := by sorry
