-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_circle_eq_polygonJ
-- name    : SpikedWishart.SoftEdge.circle_eq_polygonJ
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T06:27:09.606784+00:00
-- url     : https://prove2.me/theorems/115237d7-4b4c-44d3-a964-c4ec4012ec8e
-- title:
--   Circle integral around $0$ equals the integral over the $\mathcal J$ steepest-descent polygon
-- statement:
--   Let $c-\rho<0<c+\rho$ and let $h$ be holomorphic on $\mathbb C\setminus\{0\}$. For the parameters of the statement, with $\omega_2=e^{2i\pi/3}$,
--
--   $$\oint_{|z-c|=\rho}h=\int_{\partial P}h,$$
--
--   where $\partial P$ is the closed polygon through the vertex, $p+t\omega_2^{\pm1}$ and the horizontal ends (segments written out in the statement).
--
--   Role: deforms the circle $\Sigma$ of $\mathcal J$ into the contour of the steepest-descent analysis.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, deformation of $\Sigma$ to the rays $p_c+te^{\pm 2i\pi/3}$, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem circle_eq_polygonJ :
    ∀ (h : ℂ → ℂ) (c ρ : ℝ), c - ρ < 0 → 0 < c + ρ →
    DifferentiableOn ℂ h {z : ℂ | z.im ≠ 0 ∨ z.re < 0 ∨ 0 < z.re} →
    ∀ (p w0 δ ℓ R : ℝ), 0 < w0 → w0 ≤ p → 0 < δ → δ ≤ ℓ → 0 ≤ R → p - ℓ / 2 - R < 0 →
    (∮ z in C((c : ℂ), ρ), h z) =
    -(∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
        h (((p - ℓ / 2 - R : ℝ) : ℂ) + (y : ℂ) * I) * I)
      - (∫ x in (0 : ℝ)..R,
          h ((p : ℂ) + (ℓ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ)))
      + (∫ t in δ..ℓ, h ((p : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ s in (0 : ℝ)..(p - w0),
          h ((w0 : ℂ) + (δ : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      + (∫ t in (0 : ℝ)..δ, h ((w0 : ℂ) + (t : ℂ) * exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((2 * Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ t in (0 : ℝ)..δ, h ((w0 : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ s in (0 : ℝ)..(p - w0),
          h ((w0 : ℂ) + (δ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      - (∫ t in δ..ℓ, h ((p : ℂ) + (t : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ x in (0 : ℝ)..R,
          h ((p : ℂ) + (ℓ : ℂ) * exp (((-2 * Real.pi / 3 : ℝ) : ℂ) * I) - (x : ℂ))) := by sorry

end SpikedWishart.SoftEdge
