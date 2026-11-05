-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_sum_lt_eq_sum_product
-- name    : PaddedDescent.F.Mark.Size.sum_lt_eq_sum_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:21.145755+00:00
-- url     : https://prove2.me/theorems/ee2325de-0d57-4e8c-b054-47b85b748259
-- title:
--   Size: sum lt eq sum product
-- statement:
--   The sum over a' < a < g as a sum over all pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L424-L432
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L424-L432

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

theorem PaddedDescent.F.Mark.Size.sum_lt_eq_sum_product (F : ℕ → ℕ → ℕ) (g : ℕ) :
    ∑ a ∈ range g, ∑ a' ∈ range a, F a' a = ∑ p ∈ (range g) ×ˢ (range g), if p.1 < p.2 then F p.1 p.2 else 0 := by sorry
