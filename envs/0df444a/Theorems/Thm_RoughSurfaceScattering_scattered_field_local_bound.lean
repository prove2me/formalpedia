-- Prove2me | Theorems.Thm_RoughSurfaceScattering_scattered_field_local_bound
-- name    : RoughSurfaceScattering.scattered_field_local_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:41:05.915423+00:00
-- url     : https://prove2.me/theorems/1e06b7d5-70d9-4595-afa8-18464fdc4caa
-- title:
--   Point-source scattered fields are locally uniformly $C^1$-bounded in both variables
-- statement:
--   Let $U(y)$ be TSP solutions for the incident point sources $\Phi_{k_+}(\cdot,y)$, $y\in D^+$, and let $x_0\in D^+$. There are $r>0$ and $C$ with
--   $$|u_+(x,y)|+|\nabla_xu_+(x,y)|\le C\qquad(x,y\in B_r(x_0)).$$
--   *Proof idea.* By uniqueness (Theorem 3.3), $u_+(\cdot,y)$ is the solution given by the integral-equation representation of Section 4, whose density depends continuously on the data. The data $-\Phi_{k_+}(\cdot,y)|_\Gamma$ and $-\partial_n\Phi_{k_+}(\cdot,y)|_\Gamma$ are uniformly bounded in the weighted spaces for $y\in B_{2r}(x_0)\Subset D^+$. Interior elliptic estimates then bound $u_+$ and $\nabla_xu_+$ on $B_r(x_0)$.
--
--   **Formalization Note** `U` is an arbitrary family of TSP solutions.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, case Γ1 ≠ Γ2, PDF pp. 22-23 (u^s_2(·, x_j) is uniformly bounded near x_0 ∈ D_2^+, since x_0 has positive distance from Γ_2).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem scattered_field_local_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (U : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU : ∀ y ∈ Dplus f, IsTSPSolution f kp km μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U y).1 (U y).2)
    (x0 : R2) (hx0 : x0 ∈ Dplus f) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ y ∈ Metric.ball x0 r, ∀ x ∈ Metric.ball x0 r,
      ‖(U y).1 x‖ ≤ C ∧ ‖fderiv ℝ (U y).1 x‖ ≤ C := by sorry

end RoughSurfaceScattering
