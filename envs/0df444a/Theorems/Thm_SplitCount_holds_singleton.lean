-- Prove2me | Theorems.Thm_SplitCount_holds_singleton
-- name    : SplitCount.holds_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:34.620304+00:00
-- url     : https://prove2.me/theorems/6758927b-d9c4-4103-aaae-3b02f0c52dbe
-- title:
--   Split Count: holds singleton
-- statement:
--   A formula with the one clause H holds exactly if a literal of H is true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L46-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L46-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint
import Theorems.Thm_CountKSat_StepCount_holds_singleton

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width

theorem SplitCount.holds_singleton (b : ℕ → Bool) (H : PCl) : Holds b [H] ↔ ∃ l ∈ H, b l.1 = l.2 := by sorry
