-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi_diff_h1_uniform
-- name    : RoughSurfaceScattering.phi_diff_h1_uniform
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T00:16:52.645908+00:00
-- url     : https://prove2.me/theorems/03090865-dfff-4338-9bea-c66a826f5fbe
-- title:
--   $\Phi_k(\cdot,z)-\Phi_0(\cdot,z)$ is bounded in $H^1(D_0)$ uniformly for $z$ in a ball
-- statement:
--   Let $k\ge0$, let $D_0\subseteq\mathbb R^2$ be a bounded open set, $z_0\in\mathbb R^2$ and $a\in\mathbb C$. There is a constant $C$ with
--
--   $$\big\|a\,(\Phi_k(\cdot,z)-\Phi_0(\cdot,z))\big\|_{H^1(D_0)}\le C\qquad\text{for all }z\in B_1(z_0).$$
--
--   The logarithmic singularities cancel: $\Phi_k(x,z)-\Phi_0(x,z)$ is a $C^1$ function of $x-z$, so it and its gradient are bounded on bounded sets. This holds even when $z\in D_0$, because a single point is a null set.
--
--   **Formalization Note** $H^1$ is the platform's `h1Norm` (with `fderiv`), and $\Phi_0$ is `Phi 0`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.2 and its proof, PDF pp. 17-21 (the step 'by the regularity of Φ_{k±} − Φ_0', using the estimates in the proof of Lemma 5.1, p. 17).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi_diff_h1_uniform (k : ℝ) (hk : 0 ≤ k) (D0 : Set R2) (hD : IsOpen D0)
    (hb : Bornology.IsBounded D0) (z0 : R2) (a : ℂ) :
    ∃ C : ℝ, ∀ z ∈ Metric.ball z0 1,
      h1Norm D0 (fun x => a * (Phi k x z - Phi 0 x z)) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
