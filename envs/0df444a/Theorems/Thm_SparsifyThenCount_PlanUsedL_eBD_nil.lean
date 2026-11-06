-- Prove2me | Theorems.Thm_SparsifyThenCount_PlanUsedL_eBD_nil
-- name    : SparsifyThenCount.PlanUsedL.eBD_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:58:52.700633+00:00
-- url     : https://prove2.me/theorems/e1d00007-f3ca-4669-91db-7704a6b36b74
-- title:
--   Plan Used L: e BD nil
-- statement:
--   On the code of the formula without clauses the merged exponent is the exponent of the plan, or n
--   if there is none.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L52-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L52-L59

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide Filter
open SparsifyThenCount.PlanUsedL
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U)

theorem SparsifyThenCount.PlanUsedL.eBD_nil {k : ℕ} (n : ℕ) (hk : 1 ≤ k) :
    eBD S pick slU (SatM.enc k ([] : Sat3.CNF n)) = (planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length).getD n := by sorry
