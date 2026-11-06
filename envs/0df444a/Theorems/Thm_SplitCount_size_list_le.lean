-- Prove2me | Theorems.Thm_SplitCount_size_list_le
-- name    : SplitCount.size_list_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:36:16.519853+00:00
-- url     : https://prove2.me/theorems/c9815097-29ad-487f-b917-4926f1345787
-- title:
--   Split Count: size list le
-- statement:
--   A list of at most k entries of size at most s has size at most k(s+1) + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L28-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L28-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_size_list_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.size_list_le {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, size x ≤ s) : size l ≤ k * (s + 1) + 1 := by sorry
