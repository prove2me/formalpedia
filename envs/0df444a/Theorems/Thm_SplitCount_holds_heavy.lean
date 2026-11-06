-- Prove2me | Theorems.Thm_SplitCount_holds_heavy
-- name    : SplitCount.holds_heavy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:43:26.870323+00:00
-- url     : https://prove2.me/theorems/6f89e250-4b4e-47f0-a7ab-4e4fa20e2d25
-- title:
--   Split Count: holds heavy
-- statement:
--   An assignment satisfies the heavy child exactly if it satisfies the node and makes no literal of
--   the heart true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L90-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L90-L98

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

theorem SplitCount.holds_heavy (b : ℕ → Bool) (x : CNode) (H : PCl) (P : PFml) (hP : ∀ Q ∈ P, ∃ C ∈ x.1, ∀ l ∈ C, l ∈ H ∨ l ∈ Q) :
    Holds b (leafF (addP P x.1, negU H ++ x.2)) ↔ Holds b (leafF x) ∧ ¬ ∃ l ∈ H, b l.1 = l.2 := by sorry
