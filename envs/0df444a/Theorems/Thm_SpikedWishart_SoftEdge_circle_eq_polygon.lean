-- Prove2me | Theorems.Thm_SpikedWishart_SoftEdge_circle_eq_polygon
-- name    : SpikedWishart.SoftEdge.circle_eq_polygon
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-04T07:52:57.852421+00:00
-- url     : https://prove2.me/theorems/903ca254-ff54-4286-84dc-005c86f84972
-- title:
--   Circle integral of a function holomorphic off $[a,b]$ equals the integral over the steepest-descent polygon
-- statement:
--   Let $a\le b$, $c-\rho<a$, $b<c+\rho$ and let $h$ be holomorphic on $\{\mathrm{Im}\,z\ne0\}\cup\{\mathrm{Re}\,z<a\}\cup\{\mathrm{Re}\,z>b\}$. For $v<a$, $v\le p$, $0<\delta\le\ell$, $R\ge0$ with $b<p+\ell/2+R$, with $\omega=e^{i\pi/3}$,
--
--   $$\oint_{|z-c|=\rho}h=\int_{\partial P}h,$$
--
--   where $\partial P$ is the closed polygon through $v$, $v+\delta\omega^{\pm1}$, $p+\delta\omega^{\pm1}$, $p+\ell\omega^{\pm1}$, $p+\ell\omega^{\pm1}+R$ (nine oriented segments, written out in the statement).
--
--   Role: deforms the circle $\Gamma$ of $\mathcal H$ into the contour of the steepest-descent analysis.
-- source:
--   J. Baik, G. Ben Arous and S. Peche, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), https://doi.org/10.1214/009117905000000233, deformation of $\Gamma$ to the rays $p_c+te^{\pm i\pi/3}$, proof of Proposition 3.1, pp. 1661-1664

import Mathlib
open Complex MeasureTheory

namespace SpikedWishart.SoftEdge

theorem circle_eq_polygon :
    ∀ (h : ℂ → ℂ) (a b c ρ : ℝ), a ≤ b → c - ρ < a → b < c + ρ →
    DifferentiableOn ℂ h {z : ℂ | z.im ≠ 0 ∨ z.re < a ∨ b < z.re} →
    ∀ (p v δ ℓ R : ℝ), v < a → v ≤ p → 0 < δ → δ ≤ ℓ → 0 ≤ R → b < p + ℓ / 2 + R →
    (∮ z in C((c : ℂ), ρ), h z) =
    (∫ y in (-(ℓ * (Real.sqrt 3 / 2)))..(ℓ * (Real.sqrt 3 / 2)),
        h (((p + ℓ / 2 + R : ℝ) : ℂ) + (y : ℂ) * I) * I)
      - (∫ x in (0 : ℝ)..R, h ((p : ℂ) + (ℓ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ)))
      - (∫ t in δ..ℓ, h ((p : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((Real.pi / 3 : ℝ) : ℂ) * I))
      - (∫ s in (0 : ℝ)..(p - v),
          h ((v : ℂ) + (δ : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      - (∫ t in (0 : ℝ)..δ, h ((v : ℂ) + (t : ℂ) * exp (((Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ t in (0 : ℝ)..δ, h ((v : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ s in (0 : ℝ)..(p - v),
          h ((v : ℂ) + (δ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (s : ℂ)))
      + (∫ t in δ..ℓ, h ((p : ℂ) + (t : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I)) *
          exp (((-Real.pi / 3 : ℝ) : ℂ) * I))
      + (∫ x in (0 : ℝ)..R,
          h ((p : ℂ) + (ℓ : ℂ) * exp (((-Real.pi / 3 : ℝ) : ℂ) * I) + (x : ℂ))) := by sorry

end SpikedWishart.SoftEdge
