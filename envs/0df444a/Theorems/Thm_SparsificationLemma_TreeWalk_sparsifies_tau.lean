-- Prove2me | Theorems.Thm_SparsificationLemma_TreeWalk_sparsifies_tau
-- name    : SparsificationLemma.TreeWalk.sparsifies_tau
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:03:43.117145+00:00
-- url     : https://prove2.me/theorems/d6d0dc76-01c3-4aa7-abf6-1ca20c111838
-- title:
--   Tree Walk: sparsifies tau
-- statement:
--   `Sparsifies` for any τ ≥ 8k with (k/τ)·log₂(e·τ·τ^(2k)) ≤ ε.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/TreeWalk/Walk.lean#L57-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/TreeWalk/Walk.lean#L57-L71

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

theorem SparsificationLemma.TreeWalk.sparsifies_tau {ε : ℝ} (hk : 1 ≤ k) (hτ : 8 * k ≤ τ)
    (hε : ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsumU τ k : ℝ)) ≤ ε) :
    Sparsifies k ε (stepK (thetaU τ) k) rootP (bsumU τ k) (leafCU τ k) (2 ^ k) := by sorry
