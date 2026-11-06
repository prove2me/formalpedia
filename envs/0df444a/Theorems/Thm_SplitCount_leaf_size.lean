-- Prove2me | Theorems.Thm_SplitCount_leaf_size
-- name    : SplitCount.leaf_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:34:30.99708+00:00
-- url     : https://prove2.me/theorems/98e7946b-587f-4bcd-b668-30c6b9d50192
-- title:
--   Split Count: leaf size
-- statement:
--   The size of the input of D at a leaf: from n₃ ≤ n + q·m, m₃ ≤ m + 3q·m, m ≤ Bl·n and n ≤ M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean#L36-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean#L36-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Leaf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ

theorem SplitCount.leaf_size {q Bl n M m n₃ : ℕ} {Ψ₃ : Fml} (hn : n ≤ M) (h1 : 1 ≤ M) (hm : m ≤ Bl * n) (g1 : ∀ C ∈ Ψ₃, C.length ≤ 3) (g2 : Below n₃ Ψ₃)
    (g4 : n₃ ≤ n + q * m) (g5 : Ψ₃.length ≤ m + 3 * (q * m)) :
    n₃ + size Ψ₃ + 1 ≤ ((1 + q * Bl) + (1 + 3 * q) * Bl * (3 * (1 + q * Bl) + 11) + 2) * M ^ 2 := by sorry
