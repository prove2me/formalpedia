-- Prove2me | Theorems.Thm_SplitCount_holds_of_leaf
-- name    : SplitCount.holds_of_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:51:30.275673+00:00
-- url     : https://prove2.me/theorems/9f2d5534-18a2-416b-b289-27107ce144c7
-- title:
--   Split Count: holds of leaf
-- statement:
--   An assignment that satisfies a leaf of the tree below x satisfies x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L123-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L123-L143

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width

theorem SplitCount.holds_of_leaf (θ : ℕ → ℕ) (k : ℕ) (a : ℕ → Bool) : ∀ (d : ℕ) (x y : CNode), y ∈ leaves (stepC θ k) d x →
    (∀ C ∈ leafF y, ∃ t ∈ C, a t.1 = t.2) → ∀ C ∈ leafF x, ∃ t ∈ C, a t.1 = t.2 := by sorry
