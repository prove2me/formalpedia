-- Prove2me | Theorems.Thm_SplitCount_holds_light
-- name    : SplitCount.holds_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:33.702311+00:00
-- url     : https://prove2.me/theorems/3f625b21-30fa-458f-98f0-01bb2d04979c
-- title:
--   Split Count: holds light
-- statement:
--   An assignment satisfies the light child exactly if it satisfies the node and makes a literal of
--   the heart true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L82-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L82-L86

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

theorem SplitCount.holds_light (b : ℕ → Bool) (x : CNode) (H : PCl) :
    Holds b (leafF (addP [H] x.1, x.2)) ↔ Holds b (leafF x) ∧ ∃ l ∈ H, b l.1 = l.2 := by sorry
