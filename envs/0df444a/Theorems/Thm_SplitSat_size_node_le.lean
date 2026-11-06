-- Prove2me | Theorems.Thm_SplitSat_size_node_le
-- name    : SplitSat.size_node_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:52.836937+00:00
-- url     : https://prove2.me/theorems/56919ee5-7866-4148-b8a4-d0d1d33e42ce
-- title:
--   Split Sat: size node le
-- statement:
--   A node (n in unary, x), where x has at most a·(n+2)^k clauses of at most k literals with
--   variables below n, has size at most (a·(2k+1) + 3)·(n+2)^(k+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L121-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L121-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.size_node_le {k n a : ℕ} {x : Fml} (hm : x.length ≤ a * (n + 2) ^ k) (hx : ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size ((List.replicate n (), x) : NFml) ≤ (a * (2 * k + 1) + 3) * (n + 2) ^ (k + 1) := by sorry
