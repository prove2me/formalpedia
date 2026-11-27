-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_scattered_local_bound
-- name    : RoughSurfaceScattering.dipole_scattered_local_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:48:58.10992+00:00
-- url     : https://prove2.me/theorems/a6dd85c8-39d6-4fd8-b727-f201ee0bbe0c
-- title:
--   Dipole scattered fields are locally uniformly $C^1$-bounded
-- statement:
--   Let $x_0\in D^+$ and $\nu\in\mathbb R^2$. There are $r>0$ and $C$ such that every TSP solution $u$ with incident dipole $\nabla_x\Phi_{k_+}(\cdot,z)\cdot\nu$, $z\in B_r(x_0)$, satisfies $|u_+(x)|+|\nabla u_+(x)|\le C$ for $x\in B_r(x_0)$.
--   By uniqueness (Theorem 3.3), $u$ is the solution given by the integral-equation representation (Section 4). Its data $-\partial_\nu\Phi_{k_+}(\cdot,z)|_\Gamma$ and $-\partial_n\partial_\nu\Phi_{k_+}(\cdot,z)|_\Gamma$ are uniformly bounded in the weighted spaces for $z\in B_{2r}(x_0)\Subset D^+$. Interior elliptic estimates give the bound on $B_r(x_0)$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, case Γ1 ≠ Γ2 with μ1 = 1 (hypersingular sources), PDF pp. 22-24 (ũ_2^s(·,x_j) is bounded near x_0 ∈ D_2^+).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_scattered_local_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (x0 : R2) (hx0 : x0 ∈ Dplus f) (ν : R2) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ z ∈ Metric.ball x0 r, ∀ u : (R2 → ℂ) × (R2 → ℂ),
      IsTSPSolution f kp km μ (incData f (dipoleSource kp z ν)).1
        (incData f (dipoleSource kp z ν)).2 u.1 u.2 →
      ∀ x ∈ Metric.ball x0 r, ‖u.1 x‖ ≤ C ∧ ‖fderiv ℝ u.1 x‖ ≤ C := by sorry

end RoughSurfaceScattering
