-- Prove2me | Theorems.Thm_SparsificationLemma_TreeWalk_iface
-- name    : SparsificationLemma.TreeWalk.iface
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:29:12.127538+00:00
-- url     : https://prove2.me/theorems/4c8d2a7d-6032-4e75-b6a4-b92aeb808db7
-- title:
--   Tree Walk: iface
-- statement:
--   What the walk needs to know about the rule on finite sets, for the thresholds `thetaU τ` with 1
--   ≤ k and 8k ≤ τ, and depth τ^(2k)·n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/TreeWalk/Walk.lean#L51-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/TreeWalk/Walk.lean#L51-L54

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
import Theorems.Thm_WidthK_ProgMain_iface

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.TreeWalk
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat UniformInK SparsificationLemma.Geo
open Groundwork.Prog.SatTopK (Sparsifies)
variable {k τ : ℕ}

theorem SparsificationLemma.TreeWalk.iface (hk : 1 ≤ k) (hτ : 8 * k ≤ τ) (n : ℕ) :
    Iface (thetaU τ) k (bsumU τ k * n) ((k - 1) * n) τ ((2 * ∑ j ∈ range k, thetaU τ j) * n) (ProgMain.Ok k n)
      (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU (thetaU τ) k τ F₀ F p t) := by sorry
