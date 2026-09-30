-- Prove2me | Theorems.Thm_TauCeti_tendsto_integral_mul_cpow_mul_I_atTop
-- name    : TauCeti.tendsto_integral_mul_cpow_mul_I_atTop
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:24.122983+00:00
-- url     : https://prove2.me/theorems/e982ed57-678d-4b25-8401-643f46e6939e
-- title:
--   Riemann--Lebesgue on a vertical line
-- statement:
--   Let $f:\mathbb R\to\mathbb C$. With the totalized Lebesgue integral described below,
--
--   $$
--   \lim_{x\to\infty}\int_{\mathbb R} f(t)x^{it}\,dt=0.
--   $$
--
--   For integrable functions this is a Riemann–Lebesgue limit in logarithmic frequency.
--
--   **Formalization Note.** The statement allows arbitrary functions: the Bochner integral is defined to be zero when its integrand is not integrable. The limit only concerns positive $x$.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Fourier/RiemannLebesgue.lean#L31-L53), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Fourier/RiemannLebesgue.lean#L31-L53

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Riemann--Lebesgue along a vertical line

Testing a function on the vertical line `Re s = c` against a Dirichlet series produces the
oscillating factor `x ^ (i t)`, which is the Fourier character of frequency `-(2π)⁻¹ log x` in
the variable `t`. Letting `x → ∞` therefore pushes the frequency out of every compact set, and the
Riemann--Lebesgue lemma makes the integral vanish.

## Main declarations

* `TauCeti.tendsto_integral_mul_cpow_mul_I_atTop`: the integral `∫ t, f t * x ^ (t * I)` tends to
  `0` as `x → ∞`, for an arbitrary `f : ℝ → ℂ`.
-/

 section

open Complex Filter MeasureTheory
open scoped FourierTransform Real Topology

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

theorem TauCeti.tendsto_integral_mul_cpow_mul_I_atTop (f : ℝ → ℂ) :
    _root_.Filter.Tendsto (fun x : ℝ ↦ ∫ t : ℝ, f t * (x : ℂ) ^ (t * _root_.Complex.I)) _root_.Filter.atTop (𝓝 0) := by sorry
