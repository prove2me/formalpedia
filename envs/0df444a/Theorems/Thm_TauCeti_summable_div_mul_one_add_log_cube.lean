-- Prove2me | Theorems.Thm_TauCeti_summable_div_mul_one_add_log_cube
-- name    : TauCeti.summable_div_mul_one_add_log_cube
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:07:13.238982+00:00
-- url     : https://prove2.me/theorems/a5787781-4334-4d2e-a629-dab7a8ab521f
-- title:
--   Abel summation turns an O(t log t) growth bound into a convergent series
-- statement:
--   Let $u:\mathbb N\to[0,\infty)$ and suppose $\sum_{1\le k\le\lfloor t\rfloor}u(k)=O(t\log t)$ as $t\to\infty$. Then
--
--   $$
--   \sum_{n=1}^{\infty}\frac{u(n)}{n(1+\log n)^3}<\infty.
--   $$
--
--   This provides a summable logarithmic weight for sequences with the indicated growth.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/AbelSummation.lean#L190-L236), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/AbelSummation.lean#L190-L236

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Consequences of Abel summation for partial sums

Mathlib's `Mathlib/NumberTheory/AbelSummation.lean` proves the summation-by-parts identity
`∑_{k ≤ x} f k c k = f x ∑_{k ≤ x} c k - ∫ f' (t) ∑_{k ≤ t} c k dt` and derives convergence
criteria from it. This file draws two further consequences from a growth hypothesis on the
partial sums `∑_{1 ≤ k ≤ t} c k`.

* **A logarithmic weight.** Mathlib's `summable_mul_of_bigO_atTop'` converts a bound on the partial
  sums of a sequence into the convergence of a weighted series, provided the weight is
  differentiable and the derivative of the weight against the partial sums admits an integrable
  majorant. This file performs that conversion once, for the weight `(t (1 + log t) ^ 3)⁻¹` and
  partial sums growing like `t log t`. The weight is written with `1 + log t` rather than `log t`
  so that it stays positive and smooth at `t = 1`, where Abel summation starts. Its derivative
  against an `O(t log t)` partial sum is `O((t (1 + log t) ^ 2)⁻¹)`, which is integrable at
  infinity by comparison with Mathlib's log-Cauchy density
  `integrableOn_Ioi_zero_inv_mul_one_add_log_sq`.
* **A power weight.** If the partial sums grow like `κ x`, then the partial sums weighted by
  `n ^ τ`, for an exponent `τ > -1`, grow like `κ x ^ (τ + 1) / (τ + 1)`. This is the step that
  moves a Tauberian conclusion for the coefficients `a n n ^ (1 - σ)` back to the coefficients
  `a n`.

## Main declarations

* `TauCeti.summable_div_mul_one_add_log_cube`: if the partial sums `∑_{1 ≤ k ≤ t} u k` of a
  nonnegative sequence are `O(t log t)`, then `∑ u n / (n (1 + log n) ^ 3)` converges.
* `TauCeti.sum_Icc_rpow_mul_eq`: the exact Abel-summation identity for the weight `t ^ τ`.
* `TauCeti.tendsto_rpow_inv_mul_sum_Icc_rpow_mul`: if `x⁻¹ ∑_{1 ≤ n ≤ x} c n → κ`, then
  `(x ^ (τ + 1))⁻¹ ∑_{1 ≤ n ≤ x} n ^ τ c n → κ / (τ + 1)` for `τ > -1`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Asymptotics Filter MeasureTheory Set
open scoped Topology

variable {t : ℝ}

/-! ### The comparison weight -/



















/-! ### The hypotheses of Abel summation -/





/-! ### The weighted series -/

theorem TauCeti.summable_div_mul_one_add_log_cube {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (hgrowth : (fun t : ℝ ↦ ∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, u k) =O[_root_.Filter.atTop] fun t : ℝ ↦ t * _root_.Real.log t) :
    _root_.Summable fun n : ℕ ↦ u n / (n * (1 + _root_.Real.log n) ^ 3) := by sorry
