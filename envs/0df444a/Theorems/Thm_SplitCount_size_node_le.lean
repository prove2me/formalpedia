-- Prove2me | Theorems.Thm_SplitCount_size_node_le
-- name    : SplitCount.size_node_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:49.463496+00:00
-- url     : https://prove2.me/theorems/4bbe4dd8-ef3e-4797-99b1-47a39814666c
-- title:
--   Split Count: size node le
-- statement:
--   The size of a node of the tree, from bounds on the formula that is counted at it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L69-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L69-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.size_node_le {w m n : ℕ} {x : CNode} (hm : (leafF x).length ≤ m) (hx : ∀ C ∈ leafF x, C.length ≤ w ∧ ∀ l ∈ C, l.1 < n) : size x ≤ 2 * (m * (w * (n + 2 + 1) + 1 + 1) + 1) := by sorry
