-- Prove2me | Theorems.Thm_SizeCircuit_addStep_two
-- name    : SizeCircuit.addStep_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:50:17.550183+00:00
-- url     : https://prove2.me/theorems/2029e8bf-911c-4a91-ae3f-bcb949b5cb0a
-- title:
--   Size Circuit: add Step two
-- statement:
--   The step if exactly two wires of the present weight wait: a half adder, and its sum is the next
--   digit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L41-L42

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

theorem SizeCircuit.addStep_two (n a u : ℕ) (nxt dig : List ℕ) (K : List GateD) : addStep n ([a, u], nxt, dig, K) =
    ((n + K.length + 1) :: nxt, [], dig ++ [n + K.length], K ++ halfAdder a u) := by sorry
