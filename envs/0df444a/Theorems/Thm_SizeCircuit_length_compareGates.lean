-- Prove2me | Theorems.Thm_SizeCircuit_length_compareGates
-- name    : SizeCircuit.length_compareGates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:32.930668+00:00
-- url     : https://prove2.me/theorems/6e31c32a-41dd-4ae7-82bd-217ac45d7447
-- title:
--   Size Circuit: length compare Gates
-- statement:
--   The comparison has one gate for each digit and one more.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L59-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.length_compareGates (N s : ℕ) (digits : List ℕ) : (compareGates N s digits).length = digits.length + 1 := by sorry
