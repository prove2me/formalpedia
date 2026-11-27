-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_away_h1
-- name    : RoughSurfaceScattering.dipole_away_h1
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:26:39.745885+00:00
-- url     : https://prove2.me/theorems/ea281238-2508-5465-a986-571e4a2e40ed
-- title:
--   Dipole TSP solutions are bounded in $H^1(D_0\setminus\bar B_{3\delta/2}(x_0))$
-- statement:
--   Under the hypotheses of Theorem 5.3, for $\delta$ small, a domain $D_0$ as there, and TSP solutions $\tilde u^{(j)}$ for the dipoles $\nabla_x\Phi_{k_+}(\cdot,x_j)\cdot n(x_0)$:
--   $$\|\tilde u_-^{(j)}\|_{H^1(D_0\setminus\bar B_{3\delta/2}(x_0))}\le C\qquad(j\ge1).$$
--   By Theorem 5.3, $\tilde u_-^{(j)}-\frac2{\mu+1}\nabla\Phi_0(\cdot,x_j)\cdot n-v_j$ is bounded in $H^1(D_0)$. Away from $x_0$ the dipole $\nabla\Phi_0(\cdot,x_j)\cdot n$ is smooth uniformly in $j$, and so is the correction $v_j$, whose density is smooth away from $x_0$.
--
--   **Formalization Note** The region is `D0 \ closedBall x0 (3δ/2)`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1 (ii)-(iii), PDF pp. 24-25 ('a direct application of Theorem 5.3', p. 24).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_away_h1 (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∀ u : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u j).1 (u j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm (D0 \ Metric.closedBall (gpt f s0) (3 * δ / 2)) (u j).2 ≤ ENNReal.ofReal C := by
  sorry

end RoughSurfaceScattering
