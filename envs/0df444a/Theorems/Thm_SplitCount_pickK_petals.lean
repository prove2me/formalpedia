-- Prove2me | Theorems.Thm_SplitCount_pickK_petals
-- name    : SplitCount.pickK_petals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:49:12.573832+00:00
-- url     : https://prove2.me/theorems/f221206d-f688-42fb-be50-a86ff80d1db5
-- title:
--   Split Count: pick K petals
-- statement:
--   Every petal Q that `pickK` returns comes from a clause of s whose literals lie in the heart or
--   in Q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L67-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L67-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint
import Theorems.Thm_CountKSat_StepCount_pickK_petals

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width

theorem SplitCount.pickK_petals {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {H : PCl} {P : PFml} (h : pickK θ k s = some (H, P)) :
    ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q := by sorry
