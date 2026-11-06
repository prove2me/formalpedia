-- Prove2me | Theorems.Thm_ThreeSatOnTree_sufficesSparse_viaC
-- name    : ThreeSatOnTree.sufficesSparse_viaC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:20:40.343226+00:00
-- url     : https://prove2.me/theorems/48893bda-5c61-407a-b1bc-a6534b6e031f
-- title:
--   Three Sat On Tree: suffices Sparse via C
-- statement:
--   **«By Lemma 4 with ε = δ/3», in Theorem 2 in its decision form: it suffices to decide whether a
--   3-CNF Φ with m ≤ Mn clauses is satisfiable, in time O(2^{δ'm})**, with Lemma 4 in the form
--   `SparsificationLemma.TreeWalk.lemSparsification_walk`: M = 2·(θ 0 + θ 1 + θ 2) for its parameter τ,
--   and S = `satC τ`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatOnTree/ThmEveryDelta.lean#L56-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatOnTree/ThmEveryDelta.lean#L56-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatOnTree_Defs
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_WidthK_Poly_Decode
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_ThreeSatOnTree_ThmEveryDelta
set_option autoImplicit false
section
section
open ThreeSatOnTree
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight SparsificationLemma.TreeWalk

theorem ThreeSatOnTree.sufficesSparse_viaC {δ : ℝ} (hδ : 0 < δ) : ∃ τ : ℕ, 24 ≤ τ ∧ SufficesSparse δ (leafCU τ 3 : ℝ) (satC τ) := by sorry
