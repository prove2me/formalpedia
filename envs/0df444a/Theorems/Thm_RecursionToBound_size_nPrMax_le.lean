-- Prove2me | Theorems.Thm_RecursionToBound_size_nPrMax_le
-- name    : RecursionToBound.size_nPrMax_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:00:10.202118+00:00
-- url     : https://prove2.me/theorems/fd13f518-68bf-4de7-8641-2c0b30f9b099
-- title:
--   Recursion To Bound: size n Pr Max le
-- statement:
--   The number of binary digits of the number of profiles: at most g·g·2 times that of the number of
--   objects, plus 1, g = 3K⁸.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L117-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L117-L122

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
import Theorems.Thm_VariableBound_Net_Main_nPrMax
import Theorems.Thm_VariableBound_Net_Main_size

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper

theorem RecursionToBound.size_nPrMax_le (K n Δ : ℕ) : Nat.size (nPrMax K n Δ) ≤ 3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n Δ) + 1 := by sorry
