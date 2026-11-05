-- Prove2me | Theorems.Thm_PaddedDescent_Col_card_tail_le
-- name    : PaddedDescent.Col.card_tail_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:39.741546+00:00
-- url     : https://prove2.me/theorems/82c03571-a16a-40cb-a57c-439c5b3c3047
-- title:
--   Col: card tail le
-- statement:
--   The tail, as a count: at most K^g·exp(−δ²s/4) colourings put at least mean + δ·s into the class
--   γ, where s is any upper bound for the mean.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L109-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L109-L133

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

theorem PaddedDescent.Col.card_tail_le (x : ι → ℝ) (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b ≤ 1) (γ : κ) {δ s : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hs : (∑ b, x b) / Fintype.card κ ≤ s) :
    (#{χ : ι → κ | (∑ b, x b) / Fintype.card κ + δ * s ≤ Wt x γ χ} : ℝ)
      ≤ (Fintype.card κ : ℝ) ^ Fintype.card ι * Real.exp (-(δ ^ 2 * s / 4)) := by sorry
