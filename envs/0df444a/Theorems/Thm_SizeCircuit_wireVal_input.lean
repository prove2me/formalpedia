-- Prove2me | Theorems.Thm_SizeCircuit_wireVal_input
-- name    : SizeCircuit.wireVal_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:49:05.783643+00:00
-- url     : https://prove2.me/theorems/57d8b61b-9b75-4f02-a34a-e99909f7a466
-- title:
--   Size Circuit: wire Val input
-- statement:
--   The input wires carry the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L136-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L136-L136

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

theorem SizeCircuit.wireVal_input (x : List Bool) (K : List GateD) {i : ℕ} (hi : i < x.length) : wireVal x K i = x.getD i false := by sorry
