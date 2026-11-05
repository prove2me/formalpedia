-- Prove2me | Theorems.Thm_PaddedDescent_Col_mean_le
-- name    : PaddedDescent.Col.mean_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:43.203114+00:00
-- url     : https://prove2.me/theorems/6c5cdd8f-b800-4ce8-9cbb-5b18cd86617f
-- title:
--   Col: mean le
-- statement:
--   If x ≤ 1 pointwise, the mean is at most g/K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L138-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L138-L143

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Definitions.Def_PaddedDescent_Col_Colouring
set_option autoImplicit false
section
section
open Finset
open PaddedDescent PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]

theorem PaddedDescent.Col.mean_le (x : ι → ℝ) (hx1 : ∀ b, x b ≤ 1) [Nonempty κ] :
    (∑ b, x b) / (Fintype.card κ : ℝ) ≤ (Fintype.card ι : ℝ) / Fintype.card κ := by sorry
