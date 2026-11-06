-- Prove2me | Theorems.Thm_SparsifyThenCount_PlanUsedL_not_le_bound
-- name    : SparsifyThenCount.PlanUsedL.not_le_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:58:47.392205+00:00
-- url     : https://prove2.me/theorems/6d1a8cee-c3e4-4ceb-9f03-1c93bc7be4a8
-- title:
--   Plan Used L: not le bound
-- statement:
--   2^n is not within D·2^(D·k²·n·r), rounded down, if D·k²·r ≤ 1/2 and n ≥ 2(D + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L64-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L64-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_PlanUsedDefs
import Definitions.Def_SparsifyThenCount_Main
import Definitions.Def_VariableBound_MainPrinted
import Definitions.Def_ClauseBound_Alg_Decode
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SparsifyThenCount_PlanUsed
set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide Filter
open SparsifyThenCount.PlanUsedL

theorem SparsifyThenCount.PlanUsedL.not_le_bound {D k n : ℕ} {r : ℝ} (hr : (D : ℝ) * (k : ℝ) ^ 2 * r ≤ 1 / 2) (hn : 2 * (D + 1) ≤ n) :
    ¬ (2 ^ n ≤ ⌊(D : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (k : ℝ) ^ 2 * n * r)⌋₊) := by sorry
