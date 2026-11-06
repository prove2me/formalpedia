-- Prove2me | Theorems.Thm_SparsificationLemma_TreeWalk_lemSparsification_walk_k
-- name    : SparsificationLemma.TreeWalk.lemSparsification_walk_k
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:27:52.145699+00:00
-- url     : https://prove2.me/theorems/0712ecd9-4250-40e3-a22f-6d4ea7843aaf
-- title:
--   Tree Walk: lem Sparsification walk k
-- statement:
--   Lemma 4 for the walk, at every width k ≥ 1: for every ε > 0 there is a τ ≥ 8k for which the
--   procedure sparsifies width k with at most 2^(εn) leaves, each with at most 2·(θ 0 + … + θ (k−1))·n
--   clauses, none of them empty.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/TreeWalk/Walk.lean#L87-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/TreeWalk/Walk.lean#L87-L94

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

theorem SparsificationLemma.TreeWalk.lemSparsification_walk_k (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℕ, 8 * k ≤ τ ∧ Sparsifies k ε (stepK (thetaU τ) k) rootP (bsumU τ k) (leafCU τ k) (2 ^ k) ∧
      ∀ (n : ℕ) (ψ : PFml), IsKCNF k n ψ → ∀ x ∈ leaves (stepK (thetaU τ) k) (bsumU τ k * n) (rootP ψ), ∀ C ∈ x, C ≠ [] := by sorry
