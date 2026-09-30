-- Prove2me | Theorems.Thm_TauCeti_LSeries_differentiableOn_mul_integral_of_isBigO
-- name    : TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:44:48.725926+00:00
-- url     : https://prove2.me/theorems/1b6f85ea-a5cb-42be-b392-f32ccd4c897f
-- title:
--   Holomorphy of a partial-summation integral
-- statement:
--   Let $f:\mathbb N\to\mathbb C$ and $r\in\mathbb R$, and suppose $A(n)=\sum_{1\le k\le n}f(k)=O(n^r)$. Then
--
--   $$
--   H(s)=s\int_1^\infty A(\lfloor t\rfloor)\,t^{-s-1}\,dt
--   $$
--
--   is holomorphic on $\operatorname{Re}s>r$.
--
--   This provides a holomorphic integral representation on the half-plane determined by cancellation in the coefficient sums.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/SumCoeff.lean#L69-L104) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/SumCoeff.lean#L69-L104

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Analytic continuation of an L-series from a bound on its partial sums

If the partial sums `A(n) = ∑_{k=1}^n f k` of a sequence `f : ℕ → ℂ` are `O(n ^ r)`, Mathlib's
`LSeries_eq_mul_integral` (from `Mathlib/NumberTheory/LSeries/SumCoeff.lean`)
writes the L-series of `f` as

`LSeries f s = s * ∫ t in Set.Ioi 1, A(⌊t⌋₊) * t ^ (-(s + 1))`

wherever `LSeries f` converges and `r < Re s`. The right-hand side makes sense on the whole
half-plane `r < Re s`, independently of the convergence of the series, and this file proves that it
is holomorphic there: it is `s` times the Mellin transform of the step function `t ↦ A(⌊t⌋₊)`
at `-s`, and Mathlib's `mellin_differentiableAt_of_isBigO_rpow` applies because the step function
vanishes on `(0, 1)` and is `O(t ^ r)` at infinity.

Together the two statements continue `LSeries f` analytically from its half-plane of convergence
to `Re s > r`; this is the classical continuation of a Dirichlet series with cancelling
coefficients by partial summation (see e.g. Tenenbaum, *Introduction to Analytic and
Probabilistic Number Theory*, Chapter II.1).

## Main results

* `TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO`: under the bound `A(n) = O(n ^ r)`,
  the function `s ↦ s * ∫ t in Set.Ioi 1, A(⌊t⌋₊) * t ^ (-(s + 1))` is
  complex-differentiable on `{s | r < s.re}`.
-/

 section

open Finset Filter MeasureTheory Complex Asymptotics

open scoped Topology

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

theorem TauCeti.LSeries.differentiableOn_mul_integral_of_isBigO (f : ℕ → ℂ) {r : ℝ}
    (hO : (fun n ↦ ∑ k ∈ _root_.Finset.Icc 1 n, f k) =O[_root_.Filter.atTop] fun n ↦ (n : ℝ) ^ r) :
    _root_.DifferentiableOn ℂ
      (fun s : ℂ ↦ s * ∫ t in _root_.Set.Ioi (1 : ℝ), (∑ k ∈ _root_.Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)))
      {s | r < s.re} := by sorry
