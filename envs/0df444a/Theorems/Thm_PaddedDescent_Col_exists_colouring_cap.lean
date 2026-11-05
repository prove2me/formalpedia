-- Prove2me | Theorems.Thm_PaddedDescent_Col_exists_colouring_cap
-- name    : PaddedDescent.Col.exists_colouring_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:50.730577+00:00
-- url     : https://prove2.me/theorems/0b935d93-3554-4ecd-bc1b-4b17d377b44e
-- title:
--   Col: exists colouring cap
-- statement:
--   **The colouring lemma with a bound M on the bits between two points.** g points, K ≥ 1 colours,
--   c a b ≤ M, δ = 1/D. If (g+2)·K·exp(−δ²·(g/K)/4) < 1, some
--   colouring has classes of fewer than 2g/K points, and from any class to any class at most U/K² +
--   3g²M/(DK²) bits, where U = Σ_{a,b} c a b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L187-L300
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Col/Colouring.lean#L187-L300

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

theorem PaddedDescent.Col.exists_colouring_cap [Nonempty κ] (c : ι → ι → ℕ) (M D : ℕ) (hM0 : 0 < M) (hD : 1 ≤ D) (hM : ∀ a b, c a b ≤ M)
    (hg : ((Fintype.card ι : ℝ) + 2) * Fintype.card κ *
      Real.exp (-((1 / (D : ℝ)) ^ 2 * ((Fintype.card ι : ℝ) / Fintype.card κ) / 4)) < 1) :
    ∃ χ : ι → κ, (∀ γ, Fintype.card κ * #{a | χ a = γ} < 2 * Fintype.card ι) ∧
      ∀ γ γ', D * Fintype.card κ ^ 2 * ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
        ≤ D * (∑ a, ∑ b, c a b) + 3 * Fintype.card ι ^ 2 * M := by sorry
