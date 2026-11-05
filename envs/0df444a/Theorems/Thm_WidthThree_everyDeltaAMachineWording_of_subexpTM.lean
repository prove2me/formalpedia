-- Prove2me | Theorems.Thm_WidthThree_everyDeltaAMachineWording_of_subexpTM
-- name    : WidthThree.everyDeltaAMachineWording_of_subexpTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:52.046091+00:00
-- url     : https://prove2.me/theorems/90e932a4-23be-4baf-a720-319e9296b383
-- title:
--   Width Three: every Delta AMachine Wording of subexp TM
-- statement:
--   If one machine decides 3-SAT within A·2^{δn} steps for every δ > 0, then for every real δ > 0
--   some machine decides 3-SAT in time at most C·2^{δn}, in the wording with a real constant C and a
--   time function t(n) ≤ C·2^{δn}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/WidthThree/Rates.lean#L57-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/WidthThree/Rates.lean#L57-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_PaperSentencesStatement
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ToTuring_EndLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_WidthThree_Rates
set_option autoImplicit false
section
section
open WidthThree
open Turing
open scoped NNReal

theorem WidthThree.everyDeltaAMachineWording_of_subexpTM (h : Sat3.SubexpTM) : PaperSentences.ThmEveryDelta := by sorry
