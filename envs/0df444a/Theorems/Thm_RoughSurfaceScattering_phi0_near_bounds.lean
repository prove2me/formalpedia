-- Prove2me | Theorems.Thm_RoughSurfaceScattering_phi0_near_bounds
-- name    : RoughSurfaceScattering.phi0_near_bounds
-- status  : Proved
-- author  : @もち
-- created : 2026-11-27T02:15:48.333421+00:00
-- url     : https://prove2.me/theorems/9cb85651-5b4d-41e9-92fd-62e3ba6ce89f
-- title:
--   Uniform $L^2(D_0)$ and $H^1(D_0\setminus\bar B_\delta)$ bounds for $\Phi_0(\cdot,x_j)$
-- statement:
--   Let $D_0\subseteq D^-$ be bounded and open, and let $x_j=x_0-(\delta/j)n(x_0)\in D^+$. For every $a\in\mathbb C$ there is $C$ such that, for all $j\ge1$,
--   $$\|a\Phi_0(\cdot,x_j)\|_{L^2(D_0)}\le C,\qquad \|a\Phi_0(\cdot,x_j)\|_{H^1(D_0\setminus\bar B_\delta(x_0))}\le C .$$
--   The logarithm is square integrable on bounded sets, uniformly in the pole. For $j\ge3$ the poles stay at distance $\ge\delta/2$ from $D_0\setminus\bar B_\delta(x_0)$. For $j=1,2$ the poles lie outside $\overline{D_0}$.
--
--   **Formalization Note** $L^2$ is the platform's `l2Norm` and $H^1$ is `h1Norm`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, PDF pp. 22-24 ('the uniform boundedness of Φ_0(x,x_j) in L^2(D_0)', p. 23).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem phi0_near_bounds (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (s0 δ : ℝ) (hδ : 0 < δ)
    (D0 : Set R2) (hD : IsOpen D0) (hb : Bornology.IsBounded D0) (hsub : D0 ⊆ Dminus f)
    (hz : ∀ j : ℕ, 1 ≤ j → gpt f s0 - (δ / (j : ℝ)) • normal f s0 ∈ Dplus f) (a : ℂ) :
    ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
      l2Norm D0 (fun x => a * Phi 0 x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) ≤
        ENNReal.ofReal C ∧
      h1Norm (D0 \ Metric.closedBall (gpt f s0) δ)
        (fun x => a * Phi 0 x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by
  sorry

end RoughSurfaceScattering
