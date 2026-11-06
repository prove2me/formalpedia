-- Prove2me | Theorems.Thm_SizeCircuit_onesAmong_inputs
-- name    : SizeCircuit.onesAmong_inputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:49.950008+00:00
-- url     : https://prove2.me/theorems/4b51707c-3414-462f-bb1d-3ff934a2d20e
-- title:
--   Size Circuit: ones Among inputs
-- statement:
--   The number of input wires that are 1 is the number of ones of the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Circuit.lean#L41-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Circuit.lean#L41-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_General
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_SizeCircuit_Compare
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Circuit
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.onesAmong_inputs (x : List Bool) (K : List GateD) : onesAmong (wireVal x K) (List.range x.length) = x.count true := by sorry
