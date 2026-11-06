-- Prove2me | Theorems.Thm_SizeCircuit_length_formulaOf
-- name    : SizeCircuit.length_formulaOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:43.116626+00:00
-- url     : https://prove2.me/theorems/3fbadf50-2ec8-41eb-98bf-fe1d9d0c6cee
-- title:
--   Size Circuit: length formula Of
-- statement:
--   Four clauses for every gate and one for the output.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L72-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L72-L74

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

theorem SizeCircuit.length_formulaOf (n : ℕ) (K : List GateD) : (formulaOf n K).length = 4 * K.length + 1 := by sorry
