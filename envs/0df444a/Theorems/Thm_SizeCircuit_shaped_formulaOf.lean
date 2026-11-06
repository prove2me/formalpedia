-- Prove2me | Theorems.Thm_SizeCircuit_shaped_formulaOf
-- name    : SizeCircuit.shaped_formulaOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:26:23.979721+00:00
-- url     : https://prove2.me/theorems/f019a696-1338-4640-8137-527de90084ee
-- title:
--   Size Circuit: shaped formula Of
-- statement:
--   The formula of a non-empty circuit whose gates read earlier wires only is a 3-CNF on the
--   variables of the wires.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L78-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L78-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.shaped_formulaOf {n : ℕ} {K : List GateD} (hK : WFa n K) (hne : K ≠ []) : Shaped 3 (n + K.length) (formulaOf n K) := by sorry
