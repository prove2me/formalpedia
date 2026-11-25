-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_diff_h1_uniform
-- name    : RoughSurfaceScattering.dipole_diff_h1_uniform
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T00:31:55.610393+00:00
-- url     : https://prove2.me/theorems/9e8af8d8-05a5-40c1-b8fc-bd7e7100ac7a
-- title:
--   $\partial_\nu(\Phi_k-\Phi_0)(\cdot,z)$ is bounded in $H^1(D_0)$ uniformly for $z$ in a ball
-- statement:
--   Let $k\ge0$, $\nu\in\mathbb R^2$, let $D_0$ be a bounded open set, $z_0\in\mathbb R^2$ and $a\in\mathbb C$. There is $C$ with
--
--   $$\big\|a\,\nabla_x(\Phi_k(x,z)-\Phi_0(x,z))\cdot\nu\big\|_{H^1(D_0)}\le C\qquad\text{for all }z\in B_1(z_0).$$
--
--   The difference $\Phi_k-\Phi_0$ is $C^1$, and its second derivatives are $O(1+|\ln|x-z||)$ (Lemma 5.1). These are square integrable on bounded sets, uniformly in $z$.
--
--   **Formalization Note** The dipole is the platform's `dipoleSource`, and $H^1$ is `h1Norm`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3 and its proof, PDF pp. 21-22 (regularity of Φ_k − Φ_0 from the proof of Lemma 5.1, p. 17).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_diff_h1_uniform (k : ℝ) (hk : 0 ≤ k) (ν : R2) (D0 : Set R2) (hD : IsOpen D0)
    (hb : Bornology.IsBounded D0) (z0 : R2) (a : ℂ) :
    ∃ C : ℝ, ∀ z ∈ Metric.ball z0 1,
      h1Norm D0 (fun x => a * (dipoleSource k z ν x - dipoleSource 0 z ν x)) ≤
        ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
