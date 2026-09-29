-- Prove2me | Theorems.Thm_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff
-- name    : UpperHalfPlane.qExpansion_coeff_sum_vAdd_eq_mul_coeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/77540804-42dc-5855-acf3-bf23975169e9
-- title:
--   q-expansion coefficients of the sum of h₀ integer translates
-- statement:
--   Let $f\colon\mathbb H\to\mathbb C$ be a function on the upper half plane and let $h_0$ be a natural number with $h_0>0$. Assume: the extension $f\circ\mathtt{ofComplex}$ of $f$ to $\mathbb C$ is periodic with period $h_0$ viewed as a real number; $f$ is differentiable as a map between the complex manifolds $\mathbb H$ and $\mathbb C$ (with respect to the model $\mathcal I(\mathbb C)$ on each side); and $f$ is bounded at $i\infty$ in the sense of `UpperHalfPlane.IsBoundedAtImInfty`. Let $m$ be a natural number. Then the $m$-th coefficient of the width-one $q$-expansion `UpperHalfPlane.qExpansion 1` of the translate sum $\tau\mapsto\sum_{j=0}^{h_0-1} f(j+\tau)$, where $j$ acts by the additive action of $\mathbb R$ on $\mathbb H$ by real translation, equals $h_0$ times the $(h_0m)$-th coefficient of the width-$h_0$ $q$-expansion `UpperHalfPlane.qExpansion (h₀ : ℝ) f` of $f$ itself; here `qExpansion h g` is the power series of Taylor coefficients at $0$ of the function of $q=e^{2\pi i\tau/h}$ induced by $g$.
--
--   This is the elementary computation, via orthogonality of the $h_0$-th roots of unity, of the Fourier expansion of the sum of the $h_0$ integer translates of an $h_0$-periodic holomorphic function bounded at the cusp: only the Fourier modes divisible by $h_0$ survive, each with multiplicity $h_0$. It is used in [`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary`](thm.html#ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary), where such traces from a larger width down to width one arise from the cosets $\Gamma T^j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in

theorem UpperHalfPlane.qExpansion_coeff_sum_vAdd_eq_mul_coeff (f : UpperHalfPlane → ℂ) (h₀ : ℕ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (h₀ : ℝ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1
        (fun τ : UpperHalfPlane => ∑ j ∈ Finset.range h₀, f (((j : ℕ) : ℝ) +ᵥ τ))) =
      (h₀ : ℂ) * PowerSeries.coeff (h₀ * m) (UpperHalfPlane.qExpansion (h₀ : ℝ) f) := by sorry
