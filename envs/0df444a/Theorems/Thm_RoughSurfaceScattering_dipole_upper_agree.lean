-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_upper_agree
-- name    : RoughSurfaceScattering.dipole_upper_agree
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:26:32.424927+00:00
-- url     : https://prove2.me/theorems/712cc6ef-3e94-5026-9f64-04a0bef46c5e
-- title:
--   If point-source scattered fields agree in $D^+$, so do the dipole scattered fields
-- statement:
--   Let $U_1(y),U_2(y)$ be TSP solutions for the point sources $\Phi_{k_+}(\cdot,y)$ and two scatterers with the same $\Gamma$ and $k_+$, and suppose their upper fields agree in $D^+$ for all $y\in D^+$. Let $z\in D^+$ and $\nu$ be given, and let $\tilde u_1,\tilde u_2$ be TSP solutions for the dipole $\nabla_x\Phi_{k_+}(\cdot,z)\cdot\nu$. Then $\tilde u_{1,+}=\tilde u_{2,+}$ in $D^+$.
--
--   The TSP is uniquely solvable (Theorem 3.3), and the solution depends linearly and continuously on the data. Hence $\tilde u_{m,+}(x)=\nabla_y u_{m,+}(x,y)\cdot\nu\big|_{y=z}$, and these derivatives agree because $u_{1,+}(x,\cdot)=u_{2,+}(x,\cdot)$ on the open set $D^+$.
--
--   **Formalization Note** The families $U_m$ are arbitrary TSP solutions; uniqueness makes them the solution operators.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1 (ii)-(iii), PDF pp. 24-25 (the dipole solutions ũ are the y-derivatives of u(·,y), by uniqueness, Theorem 3.3).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_upper_agree (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp k1 k2 μ1 μ2 : ℝ)
    (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f, IsTSPSolution f kp k1 μ1 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f, IsTSPSolution f kp k2 μ2 (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f, ∀ y ∈ Dplus f, (U1 y).1 x = (U2 y).1 x)
    (z : R2) (hz : z ∈ Dplus f) (ν : R2) (u1 u2 : (R2 → ℂ) × (R2 → ℂ))
    (hu1 : IsTSPSolution f kp k1 μ1 (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 u1.1 u1.2)
    (hu2 : IsTSPSolution f kp k2 μ2 (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 u2.1 u2.2) :
    ∀ x ∈ Dplus f, u1.1 x = u2.1 x := by sorry

end RoughSurfaceScattering
