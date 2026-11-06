-- Prove2me | Theorems.Thm_SizeCircuit_wireVal_of_le
-- name    : SizeCircuit.wireVal_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:57.207194+00:00
-- url     : https://prove2.me/theorems/f55c15df-089d-4fa8-9e58-9a9502105b33
-- title:
--   Size Circuit: wire Val of le
-- statement:
--   Beyond the last wire the value is 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L144-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L144-L147

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.wireVal_of_le (x : List Bool) (K : List GateD) {i : ℕ} (hi : x.length + K.length ≤ i) : wireVal x K i = false := by sorry
