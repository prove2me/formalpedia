-- Prove2me | Theorems.Thm_SparsifyThenCount_stPlanUsed
-- name    : SparsifyThenCount.stPlanUsed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:58:53.221192+00:00
-- url     : https://prove2.me/theorems/331dfe67-4e99-4da3-948f-8b58d867dcae
-- title:
--   Sparsify Then Count: st Plan Used
-- statement:
--   If some function A with the exponent function `VariableBound.eBD S pick slU` is an algorithm for
--   the rates rn and rm, and rn tends to 0, then for every width k ≥ 1 and all large n the plan exists
--   on the code of (k, φ), for every k-CNF φ on n
--   variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L104-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L104-L135

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
open PlanUsedL

theorem SparsifyThenCount.stPlanUsed : StPlanUsed := by sorry
