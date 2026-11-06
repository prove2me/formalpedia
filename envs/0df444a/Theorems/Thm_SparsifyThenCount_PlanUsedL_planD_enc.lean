-- Prove2me | Theorems.Thm_SparsifyThenCount_PlanUsedL_planD_enc
-- name    : SparsifyThenCount.PlanUsedL.planD_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:41:21.809809+00:00
-- url     : https://prove2.me/theorems/c5ea5055-2f62-4ad5-8f34-77de9259330d
-- title:
--   Plan Used L: plan D enc
-- statement:
--   On the code of (k, φ), k ≥ 1, φ a k-CNF on n variables, the plan is that for k and n: it does
--   not depend on φ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L40-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/PlanUsed.lean#L40-L45

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

theorem SparsifyThenCount.PlanUsedL.planD_enc {k n : ℕ} (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) :
    planD S pick slU (SatM.enc k φ) = planAtD S k n (pick (root17 n)).2 (slU (pick (root17 n)).1).length := by sorry
