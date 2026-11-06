-- Prove2me | Theorems.Thm_SplitSat_sum_size_le
-- name    : SplitSat.sum_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:16.06935+00:00
-- url     : https://prove2.me/theorems/163bee06-dd07-4cb5-9f75-c5a91b66249a
-- title:
--   Split Sat: sum size le
-- statement:
--   The sum of (size + 1) over a list whose members have size at most s is at most (length)·(s+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L86-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L86-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Prog_sum_size_le
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.sum_size_le {α : Type} [HasSize α] {s : ℕ} (l : List α) (hs : ∀ x ∈ l, size x ≤ s) :
    (l.map fun x => size x + 1).sum ≤ l.length * (s + 1) := by sorry
