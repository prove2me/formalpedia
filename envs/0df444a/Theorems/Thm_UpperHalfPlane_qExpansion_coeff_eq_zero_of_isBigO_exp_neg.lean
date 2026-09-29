-- Prove2me | Theorems.Thm_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg
-- name    : UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/6db56a24-e53c-5753-9a4a-9f3d7372acb6
-- title:
--   Exponential decay at i∞ kills low q-expansion coefficients
-- statement:
--   Let $f\colon\mathbb H\to\mathbb C$ be a function on the upper half-plane subject to four hypotheses: the composite of `UpperHalfPlane.ofComplex` with $f$ (that is, $f$ viewed as a function on $\mathbb C$ via the retraction sending points off the open upper half-plane to a fixed base point) is periodic with period $1$; $f$ is differentiable with respect to the model with corners $\mathcal I(\mathbb C)$ on source and target, i.e. holomorphic on $\mathbb H$; $f$ is bounded at $i\infty$ in the sense of `UpperHalfPlane.IsBoundedAtImInfty`; and, for a given real number $L$, one has $f(\tau)=O\big(e^{-2\pi L\,\mathrm{Im}\,\tau}\big)$ along the filter `UpperHalfPlane.atImInfty`. Then for every natural number $n$ with $n<L$ (as real numbers), the $n$-th coefficient of the $q$-expansion of $f$ with period $1$, `PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)`, is zero.
--
--   This is the standard vanishing criterion for the Fourier coefficients of a $1$-periodic holomorphic function whose decay at $i\infty$ beats $e^{-2\pi L\,\mathrm{Im}\,\tau}$: all coefficients in degrees below $L$ vanish. It is used here in [`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary`](thm.html#ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary), where the contributions of the remaining cusps to a $q$-expansion must be shown to be concentrated in high degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in

theorem UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg (f : UpperHalfPlane → ℂ)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (L : ℝ) (hO : f =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * L) * τ.im))
    (n : ℕ) (hn : (n : ℝ) < L) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) = 0 := by sorry
