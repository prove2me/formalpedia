-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_sum_length_tst_le
-- name    : PaddedDescent.F.Mark.Size.sum_length_tst_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:51.412682+00:00
-- url     : https://prove2.me/theorems/824f46d1-391c-4080-b7e5-107158f78ab8
-- title:
--   Size: sum length tst le
-- statement:
--   All the strings of layer i together have at most k − 1 bits for each clause of the layer, if the
--   clauses have at most k literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L157-L192
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L157-L192

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.sum_length_tst_le (k i : ℕ) (hk : ∀ C ∈ Ls.getD i [], C.length ≤ k) :
    ∑ p ∈ (range g) ×ˢ (range g), (if p.1 < p.2 then (tst g n Ls p.1 p.2 i).length else 0) ≤ (k - 1) * (Ls.getD i []).length := by sorry
