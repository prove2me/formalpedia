-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi_decay
-- name    : RoughSurfaceScattering.phi_decay
-- status  : Proved
-- author  : @もち
-- created : 2026-11-27T02:01:38.662107+00:00
-- url     : https://prove2.me/theorems/d402032c-3c57-5f8f-bba8-196e2cd33e73
-- title:
--   $\Phi_k$ and $\nabla\Phi_k$ decay like $|x-z|^{-1/2}$
-- statement:
--   For $k>0$ there is $C$ such that for all $z,x$ with $|x-z|\ge1$:
--   $$|\Phi_k(x,z)|\le C|x-z|^{-1/2},\qquad\|\nabla_x\Phi_k(x,z)\|\le C|x-z|^{-1/2}.$$
--   Write the radial profile as $g(r)$, which satisfies Bessel's equation $g''+g'/r+k^2g=0$. Then $u=\sqrt r\,g$ satisfies $u''=-(k^2+\tfrac1{4r^2})u$, and the energy $E=u'^2+(k^2+\tfrac1{4r^2})u^2$ has $E'=-u^2/(2r^3)\le0$. Hence $u$ and $u'$ are bounded, which gives the decay of $g$ and $g'$.
--
--   **Formalization Note** The constant is uniform in the source point $z$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 2 (behaviour of H_0^{(1)}, H_1^{(1)} at infinity; used for estimate (2.4) and Lemma 2.4).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi_decay (k : ℝ) (hk : 0 < k) :
    ∃ C : ℝ, ∀ z x : R2, 1 ≤ ‖x - z‖ →
      ‖Phi k x z‖ ≤ C * ‖x - z‖ ^ (-(1 / 2 : ℝ)) ∧
      ‖fderiv ℝ (fun x' => Phi k x' z) x‖ ≤ C * ‖x - z‖ ^ (-(1 / 2 : ℝ)) := by sorry

end RoughSurfaceScattering
