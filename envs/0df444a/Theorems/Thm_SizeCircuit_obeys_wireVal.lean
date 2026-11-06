-- Prove2me | Theorems.Thm_SizeCircuit_obeys_wireVal
-- name    : SizeCircuit.obeys_wireVal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:36:35.98566+00:00
-- url     : https://prove2.me/theorems/fc0ea577-088c-4114-9a5e-a8ae25403c8e
-- title:
--   Size Circuit: obeys wire Val
-- statement:
--   The values of the wires obey the circuit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L133-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L133-L133

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

theorem SizeCircuit.obeys_wireVal (x : List Bool) (K : List GateD) (h : WFa x.length K) : Obeys (wireVal x K) x.length K := by sorry
