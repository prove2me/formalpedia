-- Prove2me | Theorems.Thm_RecursionToBound_oneOutputCost
-- name    : RecursionToBound.oneOutputCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:12:39.500443+00:00
-- url     : https://prove2.me/theorems/8d474595-bc69-4bda-a865-a741266d9d15
-- title:
--   Recursion To Bound: one Output Cost
-- statement:
--   «Hence the number of satisfying assignments of Φ is computed in time 2^{O(ekn·log Δ)}» (Step 4
--   of Appendix D): for large n, the level ℓ of n, 3 ≤ k ≤ (log n)^(1/4) and 2 ≤ Δ ≤ (log n)^(4kC₀) the
--   exponent for one output with this Δ is at most A·e_ℓ·k·n·log Δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L278-L350
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/OneOutput.lean#L278-L350

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

theorem RecursionToBound.oneOutputCost : OneOutputCost := by sorry
