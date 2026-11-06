-- Prove2me | Theorems.Thm_SizeCircuit_eval_eq_wireVal
-- name    : SizeCircuit.eval_eq_wireVal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:37:49.067578+00:00
-- url     : https://prove2.me/theorems/e7ea3ede-67be-4a14-bf5e-c9b768718eca
-- title:
--   Size Circuit: eval eq wire Val
-- statement:
--   The output of a circuit is the value of its last wire.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L139-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L139-L141

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

theorem SizeCircuit.eval_eq_wireVal (x : List Bool) (K : List GateD) : eval (toC K) x = wireVal x K (x.length + K.length - 1) := by sorry
