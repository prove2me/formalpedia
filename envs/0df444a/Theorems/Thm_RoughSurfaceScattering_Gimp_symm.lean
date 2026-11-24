-- Prove2me | Theorems.Thm_RoughSurfaceScattering_Gimp_symm
-- name    : RoughSurfaceScattering.Gimp_symm
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T11:33:42.51746+00:00
-- url     : https://prove2.me/theorems/83f0d015-b33a-47ee-a64e-278c93934131
-- title:
--   Symmetry of the impedance half-plane Green's function: $G_k^{\pm(I)}(x,y;a)=G_k^{\pm(I)}(y,x;a)$
-- statement:
--   Let $k,a,\sigma\in\mathbb R$ and let
--
--   $$G_k^{(I)}(x,y;a)=\Phi_k(x,y)+\Phi_k(x,y'_a)+P_k^{\sigma}(x-y'_a),\qquad y'_a=(y_1,2a-y_2),$$
--
--   be the impedance Green's function of the half plane of eq. (2.8), with $\sigma=\pm1$ selecting $P_k^\pm$. Then it is symmetric:
--
--   $$G_k^{(I)}(x,y;a)=G_k^{(I)}(y,x;a)\qquad\text{for all }x,y\in\mathbb R^2 .$$
--
--   The fundamental solution $\Phi_k(x,y)$ depends only on $|x-y|$. Moreover $x-y'_a=(x_1-y_1,\ x_2+y_2-2a)$ and $y-x'_a=(y_1-x_1,\ x_2+y_2-2a)$ have the same length and the same second component, and $P_k^\pm(z)$ depends only on $|z|$ and $z_2$. Symmetry of the Green's function is the basic ingredient of reciprocity relations for the scattered fields.
--
--   **Formalization Note** The statement holds for every $\sigma$, $k$ and $a$, as a property of the platform's `Gimp`, including the conventions used where the formulas are singular.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 2, eq. (2.8), PDF p. 7 (G_k^{±(I)}(x,y;a) = Φ_k(x,y) + Φ_k(x,y'_a) + P_k^±(x − y'_a)); symmetry of Green's functions, the basic ingredient of reciprocity relations.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem Gimp_symm (k a σ : ℝ) (x y : R2) : Gimp k a σ x y = Gimp k a σ y x := by sorry

end RoughSurfaceScattering
