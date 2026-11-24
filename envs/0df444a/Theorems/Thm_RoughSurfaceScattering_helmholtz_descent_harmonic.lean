-- Prove2me | Theorems.Thm_RoughSurfaceScattering_helmholtz_descent_harmonic
-- name    : RoughSurfaceScattering.helmholtz_descent_harmonic
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T05:48:49.128418+00:00
-- url     : https://prove2.me/theorems/5b8dab79-08c2-4a2b-ad64-b645b54d98a9
-- title:
--   Method of descent: $u(x_1,x_2)e^{kx_3}$ is harmonic when $\Delta u+k^2u=0$
-- statement:
--   Let $G\subseteq\mathbb R^2$ be open, $k\in\mathbb R$, and let $u\in C^2(G)$ satisfy $\Delta u+k^2u=0$ in $G$. Define on $\mathbb R^3$
--
--   $$v(y_1,y_2,y_3)=u(y_1,y_2)\,e^{k y_3}.$$
--
--   Then $v$ is harmonic on the open set $\{y\in\mathbb R^3:(y_1,y_2)\in G\}$:
--
--   $$\Delta_{\mathbb R^3}v=\big(\Delta u+k^2u\big)(y_1,y_2)\,e^{ky_3}=0 .$$
--
--   This reduces regularity questions for the two-dimensional Helmholtz equation to harmonic functions in three variables. Combined with the analyticity of harmonic functions it gives the analyticity of Helmholtz solutions.
--
--   **Formalization Note** Harmonicity is Mathlib's `InnerProductSpace.HarmonicOnNhd` on `EuclideanSpace ℝ (Fin 3)`; the point $(y_1,y_2)$ is `pt (y 0) (y 1)`.
-- source:
--   Method of descent (classical; e.g. used in D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 3rd ed., to transfer properties between the Laplace and Helmholtz equations). Supports Wu–Yang, arXiv:2406.06129v2, proof of Theorem 6.1, PDF p. 22.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem helmholtz_descent_harmonic (k : ℝ) (G : Set R2) (hG : IsOpen G) (u : R2 → ℂ)
    (hu : ContDiffOn ℝ 2 u G) (hH : IsHelmholtzOn G k u) :
    InnerProductSpace.HarmonicOnNhd
      (fun y : EuclideanSpace ℝ (Fin 3) => u (pt (y 0) (y 1)) * (Real.exp (k * y 2) : ℂ))
      {y : EuclideanSpace ℝ (Fin 3) | pt (y 0) (y 1) ∈ G} := by sorry

end RoughSurfaceScattering
