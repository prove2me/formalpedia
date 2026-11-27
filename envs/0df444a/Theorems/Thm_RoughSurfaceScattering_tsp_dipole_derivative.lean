-- Prove2me | Theorems.Thm_RoughSurfaceScattering_tsp_dipole_derivative
-- name    : RoughSurfaceScattering.tsp_dipole_derivative
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T03:02:49.268411+00:00
-- url     : https://prove2.me/theorems/e31414fc-1e9e-51bd-9a42-15826645212e
-- title:
--   The dipole scattered field is the source derivative of the point-source scattered field
-- statement:
--   Let $U(y)$, $y\in D^+$, be TSP solutions for the incident point sources $\Phi_{k_+}(\cdot,y)$. Let $u$ be a TSP solution for the incident dipole $\nabla_x\Phi_{k_+}(\cdot,z)\cdot\nu$, $z\in D^+$. Then for every $x\in D^+$,
--   $$\frac{d}{dt}\Big|_{t=0}u_+(x;\,z-t\nu)=\tilde u_+(x).$$
--   *Proof idea.* By uniqueness (Theorem 3.3), $U(y)$ is the solution produced by Theorem 4.3, which depends linearly and continuously on the data. The data $y\mapsto(-\Phi_{k_+}(\cdot,y),-\partial_n\Phi_{k_+}(\cdot,y))|_\Gamma$ are differentiable in the weighted $BC^{1,\alpha}\times BC^{0,\alpha}$ norms for $y$ off $\Gamma$. The $t$-derivative at $t=0$ of the data for $y=z-t\nu$ is the dipole data, since $\frac{d}{dt}\Phi(x,z-t\nu)|_{t=0}=\nabla_x\Phi(x,z)\cdot\nu$. Hence the difference quotients of the solutions converge to the dipole solution, pointwise in $D^+$.
--
--   **Formalization Note** `U` and `u` are arbitrary TSP solutions; uniqueness identifies them with the solution operator.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 3.3 (uniqueness) and Theorem 4.3 (existence, continuous dependence); used in the proof of Theorem 6.1 (ũ(·, z) = ∇_x Φ-data solution = derivative in the source point of u(·, y), by linearity, continuity and uniqueness).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem tsp_dipole_derivative (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (U : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU : ∀ y ∈ Dplus f, IsTSPSolution f kp km μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U y).1 (U y).2)
    (z : R2) (hz : z ∈ Dplus f) (ν : R2) (u : (R2 → ℂ) × (R2 → ℂ))
    (hu : IsTSPSolution f kp km μ (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 u.1 u.2) :
    ∀ x ∈ Dplus f, HasDerivAt (fun t : ℝ => (U (z - t • ν)).1 x) (u.1 x) 0 := by sorry

end RoughSurfaceScattering
