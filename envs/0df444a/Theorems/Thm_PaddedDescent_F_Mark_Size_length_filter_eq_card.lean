-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_length_filter_eq_card
-- name    : PaddedDescent.F.Mark.Size.length_filter_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:43:13.046385+00:00
-- url     : https://prove2.me/theorems/bb80b527-dc2a-42f8-b201-b5d704549814
-- title:
--   Size: length filter eq card
-- statement:
--   The length of a filtered list of the numbers below M, as the number of elements of a finite set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L115-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L115-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.length_filter_eq_card (M : ℕ) (p : ℕ → Bool) : ((List.range M).filter p).length = #((range M).filter fun e => p e = true) := by sorry
