-- Prove2me | Theorems.Thm_RecursionToBound_exponentIsWithinTheBound
-- name    : RecursionToBound.exponentIsWithinTheBound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:13:53.905192+00:00
-- url     : https://prove2.me/theorems/7df9cec9-8908-4797-91e1-a2bcf719ea0e
-- title:
--   Recursion To Bound: exponent Is Within The Bound
-- statement:
--   «The time is 2^(2en)·n^{O(k)}·2^{O(ekn·log Δ)} = 2^{O(k²·e·n·log(k/e))}, because k·log n ≤ en
--   for large n» (Step 5 of Appendix D): the exponent of the padding string where there is a plan is at
--   most A·k²·e_ℓ·n·log(k/e_ℓ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Exponent.lean#L167-L245
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Exponent.lean#L167-L245

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_OneOutput
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_RecursionToBound_Exponent
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen.Rate ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper

theorem RecursionToBound.exponentIsWithinTheBound : ExponentIsWithinTheBound := by sorry
