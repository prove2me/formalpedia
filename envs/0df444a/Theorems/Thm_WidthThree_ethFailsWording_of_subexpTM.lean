-- Prove2me | Theorems.Thm_WidthThree_ethFailsWording_of_subexpTM
-- name    : WidthThree.ethFailsWording_of_subexpTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:46.205797+00:00
-- url     : https://prove2.me/theorems/18095198-d41c-4a75-8ae7-9e48d631b0e2
-- title:
--   Width Three: eth Fails Wording of subexp TM
-- statement:
--   If one machine decides 3-SAT within A·2^{δn} steps for every δ > 0, then the exponential time
--   hypothesis, in the form «s_k > 0 for all k ≥ 3», fails: it fails at k = 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/WidthThree/Rates.lean#L65-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/WidthThree/Rates.lean#L65-L65

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

theorem WidthThree.ethFailsWording_of_subexpTM (h : Sat3.SubexpTM) : ¬ PaperSentences.ETH := by sorry
