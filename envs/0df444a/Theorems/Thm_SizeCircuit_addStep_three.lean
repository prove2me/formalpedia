-- Prove2me | Theorems.Thm_SizeCircuit_addStep_three
-- name    : SizeCircuit.addStep_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:48:24.020222+00:00
-- url     : https://prove2.me/theorems/1502ee4c-1e8c-4889-84e9-38dc9e91201d
-- title:
--   Size Circuit: add Step three
-- statement:
--   The step if at least three wires of the present weight wait: a full adder.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L36-L37

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

theorem SizeCircuit.addStep_three (n a u w : ℕ) (r nxt dig : List ℕ) (K : List GateD) : addStep n (a :: u :: w :: r, nxt, dig, K) =
    ((n + K.length + 1) :: r, (n + K.length + 4) :: nxt, dig, K ++ fullAdder (n + K.length) a u w) := by sorry
