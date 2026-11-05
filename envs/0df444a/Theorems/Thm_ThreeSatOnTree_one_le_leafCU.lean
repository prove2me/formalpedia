-- Prove2me | Theorems.Thm_ThreeSatOnTree_one_le_leafCU
-- name    : ThreeSatOnTree.one_le_leafCU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:20:21.617751+00:00
-- url     : https://prove2.me/theorems/cb993734-f027-460c-83a5-4a96ed6c20b5
-- title:
--   Three Sat On Tree: one le leaf CU
-- statement:
--   The constant M = 2·(θ 0 + θ 1 + θ 2) is at least 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatOnTree/ThmEveryDelta.lean#L44-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/ThreeSatOnTree/ThmEveryDelta.lean#L44-L50

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

theorem ThreeSatOnTree.one_le_leafCU (τ : ℕ) : (1 : ℝ) ≤ (leafCU τ 3 : ℝ) := by sorry
