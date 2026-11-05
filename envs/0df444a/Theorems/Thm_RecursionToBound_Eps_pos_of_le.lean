-- Prove2me | Theorems.Thm_RecursionToBound_Eps_pos_of_le
-- name    : RecursionToBound.Eps.pos_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:14:26.980001+00:00
-- url     : https://prove2.me/theorems/48fde681-26f0-43e4-b179-0fcbaed124f5
-- title:
--   Eps: pos of le
-- statement:
--   If 0 < e ≤ r, then numerator and denominator of r are positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Tree.lean#L64-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Tree.lean#L64-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_StepSparsify_CalLeaves
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Main
import Definitions.Def_ClauseBound_Alg_Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_RecursionToBound_Tree
set_option autoImplicit false
section
section
open RecursionToBound
open Finset Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound
open PaddedDescent.F.Mark (occ)
open Sat3 (CNF)
open RecursionToBound.Eps

theorem RecursionToBound.Eps.pos_of_le {r : ℕ × ℕ} {e : ℝ} (he : 0 < e) (h : e ≤ (r.1 : ℝ) / (r.2 : ℝ)) : 0 < r.1 ∧ 0 < r.2 := by sorry
