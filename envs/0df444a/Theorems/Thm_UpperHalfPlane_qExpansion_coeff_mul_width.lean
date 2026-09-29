-- Prove2me | Theorems.Thm_UpperHalfPlane_qExpansion_coeff_mul_width
-- name    : UpperHalfPlane.qExpansion_coeff_mul_width
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/3609f650-c6e7-5cf2-ac9f-2477576a116f
-- title:
--   Change of width in a q-expansion
-- statement:
--   Let $f\colon\mathbb H\to\mathbb C$ be a function on the upper half-plane, let $h_0$ be a real number with $h_0>0$, assume that the extension $f\circ$ `UpperHalfPlane.ofComplex` of $f$ to $\mathbb C$ is periodic with period $h_0$, that $f$ is holomorphic in the sense of being `MDifferentiable` from the model $\mathcal I(\mathbb C)$ on $\mathbb H$ to $\mathcal I(\mathbb C)$, and that $f$ satisfies `UpperHalfPlane.IsBoundedAtImInfty`, i.e. $f$ is bounded on $\{\operatorname{Im}\tau\ge A\}$ for some $A$. Let $m'$ be a natural number with $m'>0$ and let $i$ be a natural number. Then the $i$-th coefficient of the $q$-expansion of $f$ of width $m'h_0$, `UpperHalfPlane.qExpansion ((m' : ℝ) * h₀) f`, equals the $(i/m')$-th coefficient (natural-number division) of the $q$-expansion of width $h_0$ when $m'\mid i$, and equals $0$ otherwise. Here the width-$h$ $q$-expansion is the power series in $q_h=\exp(2\pi i\tau/h)$ attached to $f$ by the Taylor coefficients at $0$ of its cusp function.
--
--   This is the standard comparison of Fourier expansions of a periodic holomorphic function taken with respect to two commensurable widths: an $h_0$-periodic function, read in the parameter $q_{m'h_0}$, has coefficients supported on the multiples of $m'$, with the same values. It is used to pass between a width $h$ arising from some $T^h$ lying in a congruence subgroup and the exact width $h_0\mid h$ of the cusp $\infty$, and is invoked in the analysis of $q$-expansions of Siegel units, of expansions of functions in the function field of a modular curve, and in the order-of-vanishing estimates at cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_qExpansion_coeff_mul_width.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in

theorem UpperHalfPlane.qExpansion_coeff_mul_width (f : UpperHalfPlane → ℂ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) h₀)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (m' : ℕ) (hm' : 0 < m') (i : ℕ) :
    PowerSeries.coeff i (UpperHalfPlane.qExpansion ((m' : ℝ) * h₀) f) =
      if m' ∣ i then PowerSeries.coeff (i / m') (UpperHalfPlane.qExpansion h₀ f) else 0 := by sorry
