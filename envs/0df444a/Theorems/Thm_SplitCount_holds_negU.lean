-- Prove2me | Theorems.Thm_SplitCount_holds_negU
-- name    : SplitCount.holds_negU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:47.298017+00:00
-- url     : https://prove2.me/theorems/8a9a0531-01bb-4fc6-9ca5-63a9b94fc722
-- title:
--   Split Count: holds neg U
-- statement:
--   The unit clauses `negU H` hold under an assignment b exactly if b makes no literal of H true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L49-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L49-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint
import Theorems.Thm_CountKSat_StepCount_holds_negU

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width

theorem SplitCount.holds_negU (b : ℕ → Bool) (H : PCl) : Holds b (negU H) ↔ ¬ ∃ l ∈ H, b l.1 = l.2 := by sorry
