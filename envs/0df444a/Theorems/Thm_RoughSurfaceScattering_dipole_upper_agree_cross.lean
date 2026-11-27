-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_upper_agree_cross
-- name    : RoughSurfaceScattering.dipole_upper_agree_cross
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:48:52.088852+00:00
-- url     : https://prove2.me/theorems/2affaa28-6ca9-5b4a-9b1f-e2d4012f7703
-- title:
--   Agreement of point-source scattered fields implies agreement of dipole scattered fields (two surfaces)
-- statement:
--   Let $u_{m,+}(x,y)$ be point-source TSP solutions for $(\Gamma_m,k_m,\mu_m)$, $m=1,2$, with $u_{1,+}(x,y)=u_{2,+}(x,y)$ for $x,y\in D_1^+\cap D_2^+$. For $z\in D_1^+\cap D_2^+$ and dipole TSP solutions $\tilde u_m$ with incident field $\nabla_x\Phi_{k_+}(\cdot,z)\cdot\nu$, we have $\tilde u_{1,+}=\tilde u_{2,+}$ on $D_1^+\cap D_2^+$.
--   By uniqueness (Theorem 3.3) and linear, continuous dependence on the data, $\tilde u_{m,+}(x)=\nabla_yu_{m,+}(x,y)\cdot\nu|_{y=z}$. These derivatives agree because the functions agree on the open set $D_1^+\cap D_2^+\ni z$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, case Γ1 ≠ Γ2 with μ1 = 1 (hypersingular sources), PDF pp. 22-24 (ũ_m = ∇_y u_m(·,y)·ν by uniqueness, Theorem 3.3).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_upper_agree_cross (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x)
    (z : R2) (hz : z ∈ Dplus f1 ∩ Dplus f2) (ν : R2) (u1 u2 : (R2 → ℂ) × (R2 → ℂ))
    (hu1 : IsTSPSolution f1 kp k1 μ1 (incData f1 (dipoleSource kp z ν)).1
      (incData f1 (dipoleSource kp z ν)).2 u1.1 u1.2)
    (hu2 : IsTSPSolution f2 kp k2 μ2 (incData f2 (dipoleSource kp z ν)).1
      (incData f2 (dipoleSource kp z ν)).2 u2.1 u2.2) :
    ∀ x ∈ Dplus f1 ∩ Dplus f2, u1.1 x = u2.1 x := by sorry

end RoughSurfaceScattering
