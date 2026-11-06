-- Prove2me | Theorems.Thm_SparsifyThenCount_stRateZero
-- name    : SparsifyThenCount.stRateZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:59:01.559146+00:00
-- url     : https://prove2.me/theorems/5648bd13-0594-431b-8e21-8799e57b04ba
-- title:
--   Sparsify Then Count: st Rate Zero
-- statement:
--   The rate log₂ log₂(n+4)/√(log₂(n+4)) tends to 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L138-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L138-L147

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

theorem SparsifyThenCount.stRateZero : StRateZero := by sorry
