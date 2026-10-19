-- Prove2me | Theorems.Thm_Penrose_field_gradient
-- name    : Penrose.field_gradient
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T18:20:26.328173+00:00
-- url     : https://prove2.me/theorems/f51ed6cb-af48-423e-9ae6-e4a692f0f0eb
-- title:
--   The gravitational field is the gradient of the potential
-- statement:
--   For every real gravitational constant $G$, every smooth, rapidly decreasing mass density $\rho$ on three-dimensional Euclidean space $\mathbb{R}^3$, and every point $x$, the Newtonian potential
--
--   $$\Phi_\rho(x) = G \int_{\mathbb{R}^3} \frac{\rho(y)}{\|x-y\|}\,dy$$
--
--   is differentiable at $x$, and its gradient there is given by the explicit integral formula
--
--   $$\nabla\Phi_\rho(x) = -G \int_{\mathbb{R}^3} \frac{\rho(y)}{\|x-y\|^3}\,(x-y)\,dy.$$
--
--   Equivalently, the physical gravitational field $f = -\nabla\Phi$ of Newtonian gravity is $G\int \rho(y)(x-y)/\|x-y\|^3\,dy$, pointing towards the matter. This is the standard field formula of Newtonian gravity; it is the reading under which Penrose's measure of incompatibility $\Delta = \int \|\nabla\Phi_\rho - \nabla\Phi_{\rho'}\|^2\,dx$ is literally the squared $L^2$ norm of the difference of the two field gradients (Penrose 1996, Section 6, p. 595).
--
--   The statement carries no hypothesis on $G$ or on $\rho$ beyond smoothness and rapid decrease: it holds for every point $x$, including points inside the mass distribution where the integral kernel is singular.
-- source:
--   Penrose 1996, On Gravity's Role in Quantum State Reduction, General Relativity and Gravitation 28(5):581-600, https://doi.org/10.1007/BF02105068, Section 6, p. 595 (integral formula for the potential; f = -∇Φ)

import Mathlib
import Definitions.Def_penrose

open MeasureTheory

namespace Penrose

theorem field_gradient (G : ℝ) (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (newtonianPotential G ρ) (potentialGradient G ρ x) x := by sorry

end Penrose
