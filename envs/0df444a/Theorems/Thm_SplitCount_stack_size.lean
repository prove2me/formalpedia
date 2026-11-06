-- Prove2me | Theorems.Thm_SplitCount_stack_size
-- name    : SplitCount.stack_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:21.02744+00:00
-- url     : https://prove2.me/theorems/280bb901-1edc-4b8a-948a-2190543723d9
-- title:
--   Split Count: stack size
-- statement:
--   **The stack.** A stack of at most Dd·n + 1 nodes, each of which carries n in unary and has at
--   most (m + n)·Sk clauses of at most max(k, 2) literals on x₀ … xₙ₋₁, has size at most
--   `stackConst k Dd Sk`·M³, for every M ≥ 1 with n ≤ M and m ≤ M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean#L117-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Leaf.lean#L117-L150

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

theorem SplitCount.stack_size {k Dd Sk n m M : ℕ} {st : List NNode} (hn : n ≤ M) (hm : m ≤ M) (h1 : 1 ≤ M) (s1 : st.length ≤ Dd * n + 1)
    (s2 : ∀ x ∈ st, x.1 = List.replicate n () ∧ (leafF x.2).length ≤ (m + n) * Sk ∧ ∀ C ∈ leafF x.2, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) :
    size st ≤ stackConst k Dd Sk * M ^ 3 := by sorry
