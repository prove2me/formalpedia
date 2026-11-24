-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi_contDiffOn
-- name    : RoughSurfaceScattering.phi_contDiffOn
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T04:01:16.158839+00:00
-- url     : https://prove2.me/theorems/6b2f26b7-c35f-484c-bff1-034657be5ac0
-- title:
--   $\Phi_k(\cdot,z)$ is $C^1$ away from the source point
-- statement:
--   Let $k>0$ and $z\in\mathbb R^2$. The fundamental solution of the Helmholtz equation
--
--   $$\Phi_k(x,z)=\frac i4H_0^{(1)}(k|x-z|),\qquad H_0^{(1)}=J_0+iY_0,$$
--
--   is continuously differentiable as a function of $x$ on $\mathbb R^2\setminus\{z\}$.
--
--   This is the regularity of the incident point source away from its pole. It is used whenever $\Phi_k(\cdot,z)$ is combined with scattered fields in $H^1$ estimates on domains not containing $z$.
--
--   **Formalization Note** $J_0$ and $Y_0$ are the series definitions `besselJ0` and `besselY0` of the platform definition file, so the statement includes the smoothness of these series on $(0,\infty)$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 2, PDF p. 4 (Φ_k(x, y) = (i/4) H_0^{(1)}(k|x − y|), the fundamental solution of the Helmholtz equation).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi_contDiffOn (k : ℝ) (hk : 0 < k) (z : R2) :
    ContDiffOn ℝ 1 (fun x => Phi k x z) {x | x ≠ z} := by sorry

end RoughSurfaceScattering
