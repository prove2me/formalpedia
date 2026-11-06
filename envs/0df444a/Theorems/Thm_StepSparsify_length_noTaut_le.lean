-- Prove2me | Theorems.Thm_StepSparsify_length_noTaut_le
-- name    : StepSparsify.length_noTaut_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:45.375825+00:00
-- url     : https://prove2.me/theorems/decd62ec-2a23-4955-be65-d081c12afb2c
-- title:
--   Step Sparsify: length no Taut le
-- statement:
--   Deleting clauses does not make the formula longer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/WalkCount.lean#L46-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/WalkCount.lean#L46-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_Walk
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_UniformInK_Tree_Stack
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSatRate_Top
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_StepSparsify_WalkCount
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Top ClauseBound.TopN UniformInK SparsificationLemma
open Groundwork.Sparsify (PFml leaves round)

theorem StepSparsify.length_noTaut_le (ψ : PFml) : (noTaut ψ).length ≤ ψ.length := by sorry
