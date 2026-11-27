-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi_sommerfeld
-- name    : RoughSurfaceScattering.phi_sommerfeld
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:01:43.286822+00:00
-- url     : https://prove2.me/theorems/d2d72062-5a0e-5387-8809-023d2c12acf8
-- title:
--   Sommerfeld radiation condition for $\Phi_k$: $\partial_r\Phi_k-ik\Phi_k=O(r^{-3/2})$
-- statement:
--   For $k>0$ there is $C$ such that for all $z,x$ with $r=|x-z|\ge1$:
--   $$\Big|\nabla_x\Phi_k(x,z)\cdot\frac{x-z}{r}-ik\,\Phi_k(x,z)\Big|\le C\,r^{-3/2}.$$
--   This is the outgoing (Sommerfeld) behaviour of $\Phi_k=\frac i4H_0^{(1)}(kr)$. It follows from the asymptotic expansion $H_0^{(1)}(t)=\sqrt{2/(\pi t)}\,e^{i(t-\pi/4)}(1+O(1/t))$ and the corresponding expansion of $H_1^{(1)}=-H_0^{(1)\prime}$.
--
--   **Formalization Note** The radial derivative is `fderiv` applied to the unit vector $(x-z)/|x-z|$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 2 (Φ_k is outgoing; Remark 2.5).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi_sommerfeld (k : ℝ) (hk : 0 < k) :
    ∃ C : ℝ, ∀ z x : R2, 1 ≤ ‖x - z‖ →
      ‖fderiv ℝ (fun x' => Phi k x' z) x (‖x - z‖⁻¹ • (x - z)) - Complex.I * k * Phi k x z‖ ≤
        C * ‖x - z‖ ^ (-(3 / 2 : ℝ)) := by sorry

end RoughSurfaceScattering
