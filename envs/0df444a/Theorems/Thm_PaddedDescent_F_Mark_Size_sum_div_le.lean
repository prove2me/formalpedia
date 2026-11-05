-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_sum_div_le
-- name    : PaddedDescent.F.Mark.Size.sum_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:47.535148+00:00
-- url     : https://prove2.me/theorems/77faddbd-b2c9-4f96-ab5e-c5d5479ce87b
-- title:
--   Size: sum div le
-- statement:
--   Rounding down term by term gives at most the rounded-down quotient of the sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L417-L421
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L417-L421

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

theorem PaddedDescent.F.Mark.Size.sum_div_le {ι : Type} (s : Finset ι) (f : ι → ℕ) (b : ℕ) : ∑ i ∈ s, f i / b ≤ (∑ i ∈ s, f i) / b := by sorry
