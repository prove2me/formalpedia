-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi_bounded_away
-- name    : RoughSurfaceScattering.phi_bounded_away
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T08:39:12.161849+00:00
-- url     : https://prove2.me/theorems/e837efba-28cc-46cb-92bf-613a3acb7fe1
-- title:
--   For $k>0$, $\Phi_k(\cdot,z)$ and its gradient are bounded away from $z$
-- statement:
--   Let $k>0$, $z\in\mathbb R^2$ and $d>0$. There is $C$ such that
--
--   $$|\Phi_k(x,z)|\le C,\qquad\|\nabla_x\Phi_k(x,z)\|\le C\qquad\text{whenever }|x-z|\ge d .$$
--
--   $\Phi_k(x,z)=\frac i4H_0^{(1)}(k|x-z|)$ and $\nabla_x\Phi_k=-\frac{ik}4H_1^{(1)}(k|x-z|)\frac{x-z}{|x-z|}$. Both are continuous for $|x-z|>0$, so it suffices to know that $H_0^{(1)}$ and $H_1^{(1)}$ are bounded on $[kd,\infty)$, which holds because they are $O(t^{-1/2})$ at infinity.
--
--   **Formalization Note** $\Phi_k$ is the platform's `Phi`, defined through the power series of $J_0$ and $Y_0$. The gradient is the `fderiv` in $x$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 2, p. 4 (decay of the Hankel functions: H_n^{(1)}(t) = O(t^{-1/2}) as t → ∞).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi_bounded_away (k : ℝ) (hk : 0 < k) (z : R2) (d : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, ∀ x : R2, d ≤ ‖x - z‖ →
      ‖Phi k x z‖ ≤ C ∧ ‖fderiv ℝ (fun x' => Phi k x' z) x‖ ≤ C := by sorry

end RoughSurfaceScattering
