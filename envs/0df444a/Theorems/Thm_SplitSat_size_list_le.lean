-- Prove2me | Theorems.Thm_SplitSat_size_list_le
-- name    : SplitSat.size_list_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:43.456888+00:00
-- url     : https://prove2.me/theorems/c058eb90-7acf-4e55-aa44-3f59a4787797
-- title:
--   Split Sat: size list le
-- statement:
--   A list of at most k members of size at most s has size at most k·(s+1) + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L97-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L97-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_size_list_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.size_list_le {α : Type} [HasSize α] {l : List α} {k s : ℕ} (hl : l.length ≤ k) (hs : ∀ x ∈ l, size x ≤ s) :
    size l ≤ k * (s + 1) + 1 := by sorry
