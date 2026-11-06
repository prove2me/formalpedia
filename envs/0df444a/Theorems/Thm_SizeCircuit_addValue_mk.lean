-- Prove2me | Theorems.Thm_SizeCircuit_addValue_mk
-- name    : SizeCircuit.addValue_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:51:16.085195+00:00
-- url     : https://prove2.me/theorems/6b3834d2-c5d8-4811-b39d-222d73fa44ca
-- title:
--   Size Circuit: add Value mk
-- statement:
--   The value of a state given by its four parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L220-L221
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L220-L221

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.addValue_mk (v : ℕ → Bool) (cur nxt dig : List ℕ) (K : List GateD) :
    addValue v (cur, nxt, dig, K) = ofWord (dig.map v) + 2 ^ dig.length * (onesAmong v cur + 2 * onesAmong v nxt) := by sorry
