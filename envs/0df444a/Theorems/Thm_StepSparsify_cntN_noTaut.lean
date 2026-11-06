-- Prove2me | Theorems.Thm_StepSparsify_cntN_noTaut
-- name    : StepSparsify.cntN_noTaut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:41.008921+00:00
-- url     : https://prove2.me/theorems/f51c21c8-1340-4a01-b2ba-9d243ae63fce
-- title:
--   Step Sparsify: cnt N no Taut
-- statement:
--   Deleting the clauses that contain a variable together with its negation does not change the
--   number of satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/WalkCount.lean#L38-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/WalkCount.lean#L38-L43

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate CountKSatRate.Top ClauseBound.TopN UniformInK SparsificationLemma
open Groundwork.Sparsify (PFml leaves round)

theorem StepSparsify.cntN_noTaut (n : ℕ) (ψ : PFml) : cntN n (noTaut ψ) = cntN n ψ := by sorry
