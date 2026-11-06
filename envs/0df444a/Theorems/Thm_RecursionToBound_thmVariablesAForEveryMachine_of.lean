-- Prove2me | Theorems.Thm_RecursionToBound_thmVariablesAForEveryMachine_of
-- name    : RecursionToBound.thmVariablesAForEveryMachine_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:12.05292+00:00
-- url     : https://prove2.me/theorems/236c6553-946a-46cd-85f8-c7475e173b00
-- title:
--   Recursion To Bound: thm Variables AFor Every Machine of
-- statement:
--   Theorem D (a) for every machine that computes the named function. Four statements on the
--   function are hypotheses: it is right, it is polynomial-time, it sparsifies unless the exponent
--   exceeds n, and it reads the width and the level from the code. `exponentIsWithinTheBound` and
--   `cutOffIsIdle` are used directly.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/End.lean#L92-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/End.lean#L92-L184

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_Exponent
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_RecursionToBound_End
set_option autoImplicit false
section
section
open RecursionToBound
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End UniformInK Wrap MainTheoremForms PairsToBound VariableBound.Paper
open Sat3 (CNF)

theorem RecursionToBound.thmVariablesAForEveryMachine_of (hRight : CountIsRight) (hPoly : CountIsPolynomialTime) (hPlan : PlanFailsOnlyAboveN) (hWidth : WidthOnTheCode) : ThmVariablesAForEveryMachine := by sorry
