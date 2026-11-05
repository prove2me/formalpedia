-- Prove2me | Theorems.Thm_PaddedDescent_Col_sum_exp_le
-- name    : PaddedDescent.Col.sum_exp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:34.517208+00:00
-- url     : https://prove2.me/theorems/ae937f4e-5e60-49f7-8fce-373f7f331406
-- title:
--   Col: sum exp le
-- statement:
--   The exponential moment, as a sum over all colourings: at most K^g·exp((θ+θ²)·mean), for 0 ≤ θ ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L59-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L59-L105

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

theorem PaddedDescent.Col.sum_exp_le (x : ι → ℝ) (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b ≤ 1) (γ : κ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∑ χ : ι → κ, Real.exp (θ * Wt x γ χ)
      ≤ (Fintype.card κ : ℝ) ^ Fintype.card ι * Real.exp ((θ + θ ^ 2) * ((∑ b, x b) / Fintype.card κ)) := by sorry
