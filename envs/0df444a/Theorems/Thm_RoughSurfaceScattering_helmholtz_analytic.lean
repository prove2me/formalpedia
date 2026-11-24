-- Prove2me | Theorems.Thm_RoughSurfaceScattering_helmholtz_analytic
-- name    : RoughSurfaceScattering.helmholtz_analytic
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T05:36:10.070235+00:00
-- url     : https://prove2.me/theorems/78a62548-89dc-4479-b531-9b258725afb4
-- title:
--   Classical solutions of the Helmholtz equation are real analytic
-- statement:
--   Let $G\subseteq\mathbb R^2$ be open, $k\in\mathbb R$, and let $u\in C^2(G)$ be a complex-valued solution of the Helmholtz equation
--
--   $$\Delta u+k^2u=0\qquad\text{in }G .$$
--
--   Then $u$ is real analytic in $G$: around every point of $G$ it is given by a convergent power series in $x_1,x_2$.
--
--   This is the classical analyticity of solutions of elliptic equations with constant coefficients. It can be proved, for instance, from Green's representation formula on small discs, whose kernel $\Phi_k(x,y)$ is analytic in $x$ away from the boundary. It is the analytic input behind both the extension of near-field data from a segment to a line and unique continuation in the proof of Theorem 6.1.
--
--   **Formalization Note** The Laplacian is Mathlib's `Laplacian.laplacian`, analyticity is `AnalyticOnNhd ℝ`, and $u$ takes values in $\mathbb C$ viewed as a real normed space.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, PDF p. 22 (procedure of [49, Theorem 4.1]); standard elliptic regularity, e.g. D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 3rd ed., Theorem 2.2 (solutions of the Helmholtz equation are analytic).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem helmholtz_analytic (k : ℝ) (G : Set R2) (hG : IsOpen G) (u : R2 → ℂ)
    (hu : ContDiffOn ℝ 2 u G) (hH : IsHelmholtzOn G k u) :
    AnalyticOnNhd ℝ u G := by sorry

end RoughSurfaceScattering
