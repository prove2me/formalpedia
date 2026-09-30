-- Prove2me | Theorems.Thm_TauCeti_LSeries_LSeriesSummable_mul_of_norm_le
-- name    : TauCeti.LSeries.LSeriesSummable_mul_of_norm_le
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:13:36.443985+00:00
-- url     : https://prove2.me/theorems/7dd2f125-e5f0-4b89-a6fb-5f3ba227ca0e
-- title:
--   Logarithmic damping gives convergence at the boundary
-- statement:
--   Let $(a_n)$ and $(W_n)$ be complex sequences. Suppose
--
--   $$
--   \sum_{1\le n\le t}|a_n|=O(t\log t)\qquad(t\to+\infty),
--   $$
--
--   and suppose that for some real $D$ one has $|W_n|\le D/(1+\log n)^3$ for all sufficiently large $n$. Then
--
--   $$
--   \sum_{n\ge1}\frac{a_nW_n}{n}\quad\text{converges absolutely}.
--   $$
--
--   This supplies a summable boundary weight from a logarithmically weakened bound on partial sums.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/Summable.lean#L38-L69) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/Summable.lean#L38-L69

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Summability at `s = 1` of a logarithmically damped Dirichlet series

A Dirichlet series whose coefficients have `O(t log t)` partial sums need not converge on the line
`Re s = 1`, but it does converge there once each coefficient is weighted by a factor of size
`O((1 + log n) ^ (-3))`: in the Abel-summation bound
`TauCeti.summable_div_mul_one_add_log_cube`, one of the three logarithms absorbs the `log t` in the
growth of the partial sums, and the remaining two leave the integrable majorant
`(t (1 + log t) ^ 2)⁻¹`.

Such a weight arises whenever a Dirichlet series is tested against a smooth compactly supported
function, whose Fourier transform decays faster than every power.

## Main declarations

* `TauCeti.LSeries.LSeriesSummable_mul_of_norm_le`: an `O((1 + log n) ^ (-3))` weighting of
  coefficients with `O(t log t)` partial sums has a Dirichlet series converging at `s = 1`.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Asymptotics Filter

variable {a W : ℕ → ℂ} {D : ℝ}

theorem TauCeti.LSeries.LSeriesSummable_mul_of_norm_le
    (hgrowth : (fun t : ℝ ↦ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, ‖a k‖) =O[_root_.Filter.atTop] fun t : ℝ ↦ t * _root_.Real.log t)
    (hW : ∀ᶠ n : ℕ in _root_.Filter.atTop, ‖W n‖ ≤ D / (1 + _root_.Real.log n) ^ 3) :
    _root_.LSeriesSummable (fun n ↦ a n * W n) 1 := by sorry
