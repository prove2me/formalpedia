-- Prove2me | Theorems.Thm_SplitCount_holds_petals
-- name    : SplitCount.holds_petals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:50:04.72508+00:00
-- url     : https://prove2.me/theorems/6ee53f80-60fe-4f30-b52d-e41c7e907df8
-- title:
--   Split Count: holds petals
-- statement:
--   If no literal of the heart H is true and s holds, then the petals hold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L56-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L56-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint
import Theorems.Thm_CountKSat_StepCount_holds_petals

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width

theorem SplitCount.holds_petals {b : ℕ → Bool} {s P : PFml} {H : PCl} (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q)
    (hH : ¬ ∃ l ∈ H, b l.1 = l.2) (hs : Holds b s) : Holds b P := by sorry
