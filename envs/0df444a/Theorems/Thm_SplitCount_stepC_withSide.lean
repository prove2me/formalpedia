-- Prove2me | Theorems.Thm_SplitCount_stepC_withSide
-- name    : SplitCount.stepC_withSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:45.088479+00:00
-- url     : https://prove2.me/theorems/fd22e9e6-e63b-470c-9d41-6e129c2e0903
-- title:
--   Split Count: step C with Side
-- statement:
--   The step of the tree only puts clauses in front of the side list and never reads it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L85-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Tree.lean#L85-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Tree
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width

theorem SplitCount.stepC_withSide (θ : ℕ → ℕ) (k : ℕ) (t : PFml) (x : CNode) :
    stepC θ k (withSide t x) = (stepC θ k x).map fun lh => (withSide t lh.1, withSide t lh.2) := by sorry
