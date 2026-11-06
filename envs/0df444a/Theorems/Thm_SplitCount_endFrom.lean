-- Prove2me | Theorems.Thm_SplitCount_endFrom
-- name    : SplitCount.endFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:47.006229+00:00
-- url     : https://prove2.me/theorems/7cc00201-1ff3-4a53-bdc3-1fd2acbda765
-- title:
--   Split Count: end From
-- statement:
--   **Corollary 6**: «For every k ≥ 3 and δ > 0 there is a deterministic algorithm that computes the
--   number of satisfying assignments of a k-CNF on n variables in time O(2^{δn}). For k = 3 this says
--   that the counting version #ETH of ETH is false.»
--   The statement is `PaperSentences.CorCounting` of PaperSentencesStatement.lean, for Turing machines.
--   Here it is drawn from the tied statement `StTiedTM` as a hypothesis: both halves take the Turing
--   machine of that statement, which simulates `COUNTsplit k ℓ τ`; the second half at k = 3, by
--   `CountKSat.EndLemmas.not_CountETH_TM_of`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Main.lean#L70-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Main.lean#L70-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_SplitCount_Main
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem SplitCount.endFrom (h : StTiedTM) : ThreeSatStatement := by sorry
