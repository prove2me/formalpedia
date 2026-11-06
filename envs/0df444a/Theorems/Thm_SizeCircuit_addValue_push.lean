-- Prove2me | Theorems.Thm_SizeCircuit_addValue_push
-- name    : SizeCircuit.addValue_push
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:00.233569+00:00
-- url     : https://prove2.me/theorems/b3ee1295-35e2-4e4e-a920-ab77d17eb0d4
-- title:
--   Size Circuit: add Value push
-- statement:
--   The value after a new digit d has been found and the next weight has become the present one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L224-L228
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L224-L228

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

theorem SizeCircuit.addValue_push (v : ℕ → Bool) (cur dig : List ℕ) (d : ℕ) (K : List GateD) :
    addValue v (cur, [], dig ++ [d], K) = ofWord (dig.map v) + 2 ^ dig.length * ((v d).toNat + 2 * onesAmong v cur) := by sorry
