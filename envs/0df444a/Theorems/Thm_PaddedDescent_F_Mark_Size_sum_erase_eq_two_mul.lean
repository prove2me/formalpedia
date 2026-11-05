-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_sum_erase_eq_two_mul
-- name    : PaddedDescent.F.Mark.Size.sum_erase_eq_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:31.742576+00:00
-- url     : https://prove2.me/theorems/767222a0-5d4f-4e54-b04b-5b819b7bbcd3
-- title:
--   Size: sum erase eq two mul
-- statement:
--   A symmetric table summed over the ordered pairs of different numbers below g is twice its sum
--   over the pairs a' < a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L394-L407
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L394-L407

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.sum_erase_eq_two_mul (F : ℕ → ℕ → ℕ) (hF : ∀ a b, F a b = F b a) (g : ℕ) :
    ∑ a ∈ range g, ∑ b ∈ (range g).erase a, F a b = 2 * ∑ a ∈ range g, ∑ a' ∈ range a, F a' a := by sorry
