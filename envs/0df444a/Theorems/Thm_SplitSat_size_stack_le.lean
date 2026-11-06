-- Prove2me | Theorems.Thm_SplitSat_size_stack_le
-- name    : SplitSat.size_stack_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:44.021379+00:00
-- url     : https://prove2.me/theorems/71f89c4a-c95d-4f90-8af1-58af2664b200
-- title:
--   Split Sat: size stack le
-- statement:
--   A stack of at most Dd·n + 1 such nodes has size at most ((Dd+1)·(a·(2k+1) + 4) + 1)·(n+2)^(k+2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L139-L161
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L139-L161

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.size_stack_le {k n a Dd : ℕ} {st : List Fml} (hl : st.length ≤ Dd * n + 1)
    (hst : ∀ x ∈ st, x.length ≤ a * (n + 2) ^ k ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    size (st.map fun y => ((List.replicate n (), y) : NFml)) ≤ ((Dd + 1) * (a * (2 * k + 1) + 4) + 1) * (n + 2) ^ (k + 2) := by sorry
