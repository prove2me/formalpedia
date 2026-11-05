-- Prove2me | Theorems.Thm_PaddedDescent_Col_exists_all_good
-- name    : PaddedDescent.Col.exists_all_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:44.430977+00:00
-- url     : https://prove2.me/theorems/a462146c-59b7-47cb-80a3-74175b44c6b2
-- title:
--   Col: exists all good
-- statement:
--   Finitely many families of weights at once: if the number of (weight, colour) pairs times
--   exp(−δ²s/4) is below 1, one colouring is good for all.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L147-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L147-L175

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

theorem PaddedDescent.Col.exists_all_good [Nonempty κ] {T : Type*} [Fintype T] (x : T → ι → ℝ) (hx0 : ∀ t b, 0 ≤ x t b) (hx1 : ∀ t b, x t b ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : (Fintype.card T : ℝ) * Fintype.card κ * Real.exp (-(δ ^ 2 * ((Fintype.card ι : ℝ) / Fintype.card κ) / 4)) < 1) :
    ∃ χ : ι → κ, ∀ t γ, Wt (x t) γ χ < (∑ b, x t b) / Fintype.card κ + δ * ((Fintype.card ι : ℝ) / Fintype.card κ) := by sorry
