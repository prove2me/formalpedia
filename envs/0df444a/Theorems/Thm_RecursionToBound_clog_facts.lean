-- Prove2me | Theorems.Thm_RecursionToBound_clog_facts
-- name    : RecursionToBound.clog_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:57:11.138194+00:00
-- url     : https://prove2.me/theorems/bbbbb1da-ccd3-44f1-b824-f50ca32e67a8
-- title:
--   Recursion To Bound: clog facts
-- statement:
--   2^⌈log₂ Δ⌉ ≤ 2Δ, 1 ≤ ⌈log₂ Δ⌉ and ⌈log₂ Δ⌉ + 1 ≤ 3·log Δ, for Δ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L259-L273
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L259-L273

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Top_ArithNat
import Definitions.Def_UniformInK_Top_ArithMaster
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_StepCost
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_OneOutput
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper

theorem RecursionToBound.clog_facts {Δ : ℕ} (hΔ : 2 ≤ Δ) : 2 ^ Nat.clog 2 Δ ≤ 2 * Δ ∧ 1 ≤ Nat.clog 2 Δ ∧ ((Nat.clog 2 Δ + 1 : ℕ) : ℝ) ≤ 3 * lg Δ := by sorry
