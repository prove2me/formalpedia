-- Prove2me | Theorems.Thm_Sendov_integral_moment_rec
-- name    : Sendov.integral_moment_rec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:52.203339+00:00
-- url     : https://prove2.me/theorems/9c9f46d1-4329-4e05-8734-c50edcb0a676
-- title:
--   Sendov: integral moment rec
-- statement:
--   **The moment, by the recurrence.**  If `D * Q t` has the integer coefficient
--   polynomials `g₀, g₁, g₂` in `α`, then the moment is a kernel computation on those integers.
--   No hypothesis beyond `D ≠ 0` is needed: this is a polynomial identity.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L204-L214
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L204-L214

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_moment_rec {n k : ℕ} {α D : ℝ} {g₀ g₁ g₂ : List ℤ} (hD : D ≠ 0)
    (hQ : ∀ t : ℝ, D * Q n α t = pev g₀ α + pev g₁ α * t + pev g₂ α * t ^ 2) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k) = irow (qrow g₀ g₁ g₂ k) 0 α / D ^ k := by sorry
