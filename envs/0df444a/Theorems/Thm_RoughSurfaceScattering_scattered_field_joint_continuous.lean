-- Prove2me | Theorems.Thm_RoughSurfaceScattering_scattered_field_joint_continuous
-- name    : RoughSurfaceScattering.scattered_field_joint_continuous
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T03:08:32.383805+00:00
-- url     : https://prove2.me/theorems/e32f0083-0e54-4315-922b-68f2e136d8c2
-- title:
--   Point-source scattered fields are jointly $C^1$-continuous in field point and source
-- statement:
--   Let $U(y)$ be TSP solutions for the point sources $\Phi_{k_+}(\cdot,y)$, $y\in D^+$, and let $x_0\in D^+$. For some $r>0$, both $(x,y)\mapsto u_+(x;y)$ and $(x,y)\mapsto\nabla_xu_+(x;y)$ are continuous on $\bar B_r(x_0)\times\bar B_r(x_0)$.
--   By uniqueness (Theorem 3.3), $U(y)$ is the solution of Section 4. Its density depends continuously on the data, and the data depend continuously on $y$ in the weighted Hölder norms for $y$ away from $\Gamma$. The representation by layer potentials then gives joint continuity of $u_+$ and $\nabla_xu_+$ for $x$ away from $\Gamma$.
--
--   **Formalization Note** `U` is an arbitrary family of TSP solutions.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 3.3 (uniqueness) and Theorem 4.3 / Section 4 (integral-equation solution); used in the proof of Theorem 6.1 (the solution depends continuously on the data; interior regularity in x).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem scattered_field_joint_continuous (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (U : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU : ∀ y ∈ Dplus f, IsTSPSolution f kp km μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U y).1 (U y).2)
    (x0 : R2) (hx0 : x0 ∈ Dplus f) :
    ∃ r > (0 : ℝ),
      ContinuousOn (fun p : R2 × R2 => (U p.2).1 p.1)
        (Metric.closedBall x0 r ×ˢ Metric.closedBall x0 r) ∧
      ContinuousOn (fun p : R2 × R2 => fderiv ℝ (U p.2).1 p.1)
        (Metric.closedBall x0 r ×ˢ Metric.closedBall x0 r) := by sorry

end RoughSurfaceScattering
