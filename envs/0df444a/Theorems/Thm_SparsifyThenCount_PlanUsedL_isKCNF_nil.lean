-- Prove2me | Theorems.Thm_SparsifyThenCount_PlanUsedL_isKCNF_nil
-- name    : SparsifyThenCount.PlanUsedL.isKCNF_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:37:01.830754+00:00
-- url     : https://prove2.me/theorems/7ecf3923-d1a2-4cb2-9669-603b4d3382ee
-- title:
--   Plan Used L: is KCNF nil
-- statement:
--   The formula without clauses is a k-CNF.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L48-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L48-L48

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
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U)

theorem SparsifyThenCount.PlanUsedL.isKCNF_nil (k n : ℕ) : SatK.IsKCNF k ([] : Sat3.CNF n) := by sorry
