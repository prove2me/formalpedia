-- Prove2me | Theorems.Thm_SizeCircuit_holds_formulaOf
-- name    : SizeCircuit.holds_formulaOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:26:17.764345+00:00
-- url     : https://prove2.me/theorems/07f206dc-5d80-4039-bb28-f1d546d5c1b4
-- title:
--   Size Circuit: holds formula Of
-- statement:
--   The formula holds exactly if the clauses of the gates hold and the variable of the output is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L90-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Gamma.lean#L90-L97

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

theorem SizeCircuit.holds_formulaOf (a : ℕ → Bool) (n : ℕ) (K : List GateD) : Holds a (formulaOf n K) ↔ Holds a (wiresFormula n K) ∧ a (n + K.length - 1) = true := by sorry
