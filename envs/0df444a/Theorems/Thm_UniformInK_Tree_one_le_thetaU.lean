-- Prove2me | Theorems.Thm_UniformInK_Tree_one_le_thetaU
-- name    : UniformInK.Tree.one_le_thetaU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:58.711642+00:00
-- url     : https://prove2.me/theorems/db26f046-694c-40d1-9078-deb722a3e2dc
-- title:
--   Tree: one le theta U
-- statement:
--   Every threshold is at least 1, if τ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Tree/Tree.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Tree/Tree.lean#L35-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Tree_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Tree_Tree
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate WidthK.Prog
open UniformInK.Tree

theorem UniformInK.Tree.one_le_thetaU {τ : ℕ} (hτ : 1 ≤ τ) : ∀ i, 1 ≤ thetaU τ i
  := by sorry
