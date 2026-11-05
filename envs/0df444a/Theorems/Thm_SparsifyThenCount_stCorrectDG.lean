-- Prove2me | Theorems.Thm_SparsifyThenCount_stCorrectDG
-- name    : SparsifyThenCount.stCorrectDG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:26.864855+00:00
-- url     : https://prove2.me/theorems/df2ba494-c2a1-46b5-9474-23155c24d453
-- title:
--   Sparsify Then Count: st Correct DG
-- statement:
--   The function for the bound in n, run with thresholds that serve, is right on every k-CNF, for
--   every k ≥ 1 and every n, when the pad has length at least 2^(eD …); given the count of a sparse
--   formula (`VariableBound.StCountD`), the budgets
--   (`VariableBound.StBudgetD`, `StRoundsDG`), the walk through the counting tree
--   (`StepSparsify.StWalkCountG`), the decoders and exhaustive counting.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Correct.lean#L50-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Correct.lean#L50-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_SparsifyThenCount_Correct
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open SparsifyThenCount
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.Correct VariableBound VariableBound.Correct VariableBound.Net
open PaddedDescent.F.Mark (WfL occ nSat)

theorem SparsifyThenCount.stCorrectDG (hC : StCountD) (hB : StBudgetD) (hR : StRoundsDG) (hWC : StepSparsify.StWalkCountG) (hD : StDecM) (hBr : StBruteC) (hDU : StDecU) : StCorrectDG := by sorry
