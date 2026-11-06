-- Prove2me | Theorems.Thm_SparsificationLemma_TreeWalk_leaf_ne_nil
-- name    : SparsificationLemma.TreeWalk.leaf_ne_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:17.635594+00:00
-- url     : https://prove2.me/theorems/8c7e6917-7fbf-4758-a771-8b3b6bc75992
-- title:
--   Tree Walk: leaf ne nil
-- statement:
--   No leaf of the tree of a k-CNF has an empty clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/TreeWalk/Walk.lean#L74-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/TreeWalk/Walk.lean#L74-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_SparsificationLemma_Geo_Thr
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_SparsificationLemma_Geo_Eps
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.TreeWalk
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat UniformInK SparsificationLemma.Geo
open Groundwork.Prog.SatTopK (Sparsifies)
variable {k τ : ℕ}

theorem SparsificationLemma.TreeWalk.leaf_ne_nil (hk : 1 ≤ k) (hτ : 8 * k ≤ τ) {n : ℕ} {ψ : PFml} (hψ : IsKCNF k n ψ) (D : ℕ) :
    ∀ x ∈ leaves (stepK (thetaU τ) k) D (rootP ψ), ∀ C ∈ x, C ≠ [] := by sorry
