-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_field_joint_continuous
-- name    : RoughSurfaceScattering.dipole_field_joint_continuous
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T03:08:37.681958+00:00
-- url     : https://prove2.me/theorems/841cb3db-2b3f-45a3-a03a-5132f3cd6ed0
-- title:
--   Dipole scattered fields are jointly $C^1$-continuous in field point and source
-- statement:
--   Let $V(z)$ be TSP solutions for the dipoles $\nabla_x\Phi_{k_+}(\cdot,z)\cdot\nu$, $z\in D^+$, and let $x_0\in D^+$. For some $r>0$, both $(x,z)\mapsto v_+(x;z)$ and $(x,z)\mapsto\nabla_xv_+(x;z)$ are continuous on $\bar B_r(x_0)\times\bar B_r(x_0)$.
--   The argument is the same as for point sources: uniqueness, continuous dependence on the data (which are smooth in $z$ off $\Gamma$), and the layer-potential representation.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 3.3 (uniqueness) and Theorem 4.3 / Section 4 (integral-equation solution); used in the proof of Theorem 6.1 (same argument as for point sources, with hypersingular data ∇_xΦ(·,z)·ν).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_field_joint_continuous (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (ν : R2) (V : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hV : ∀ z ∈ Dplus f, IsTSPSolution f kp km μ (incData f (dipoleSource kp z ν)).1
      (incData f (dipoleSource kp z ν)).2 (V z).1 (V z).2)
    (x0 : R2) (hx0 : x0 ∈ Dplus f) :
    ∃ r > (0 : ℝ),
      ContinuousOn (fun p : R2 × R2 => (V p.2).1 p.1)
        (Metric.closedBall x0 r ×ˢ Metric.closedBall x0 r) ∧
      ContinuousOn (fun p : R2 × R2 => fderiv ℝ (V p.2).1 p.1)
        (Metric.closedBall x0 r ×ˢ Metric.closedBall x0 r) := by sorry

end RoughSurfaceScattering
