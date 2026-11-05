-- Prove2me | Theorems.Thm_WidthThree_ethFails_of_subexpTM
-- name    : WidthThree.ethFails_of_subexpTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:35.988896+00:00
-- url     : https://prove2.me/theorems/a0661b10-b926-49e4-8f18-21143fb3275a
-- title:
--   Width Three: eth Fails of subexp TM
-- statement:
--   If one machine decides 3-SAT within A·2^{δn} steps for every δ > 0, then the exponential time
--   hypothesis, in the form «the infimum of the δ for which 3-SAT is in time O(2^{δn}) is positive»,
--   fails.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/WidthThree/Rates.lean#L52-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/WidthThree/Rates.lean#L52-L52

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

theorem WidthThree.ethFails_of_subexpTM (h : Sat3.SubexpTM) : ¬ Sat3.ETH_TM := by sorry
