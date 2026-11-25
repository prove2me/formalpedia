-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_h1_core
-- name    : RoughSurfaceScattering.dipole_h1_core
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T05:54:42.173169+00:00
-- url     : https://prove2.me/theorems/ab133295-1693-4c21-9e3f-d345382c8056
-- title:
--   $H^1$ part of Theorem 5.3 (with $\Phi_{k_-}$): $\tilde u_-^{(j)}-\frac2{\mu+1}\partial_{n_0}\Phi_{k_-}(\cdot,x_j)-v_j$ is bounded
-- statement:
--   Under the hypotheses of Theorem 5.3, let $(\tilde u_+^{(j)},\tilde u_-^{(j)})$ solve the TSP with the incident dipole $\nabla_x\Phi_{k_+}(x,x_j)\cdot n(x_0)$. Then, uniformly in $j$,
--
--   $$\Big\|\tilde u_-^{(j)}-\frac2{\mu+1}\nabla_x\Phi_{k_-}(x,x_j)\cdot n(x_0)-v_j\Big\|_{H^1(D_0)}\le C .$$
--
--   *Proof idea (paper).* By Lemma 2.4, $\nabla\Phi_{k_+}(\cdot,y_j)\cdot n_0$ satisfies the UPRC and $\nabla\Phi_{k_-}(\cdot,x_j)\cdot n_0$ the DPRC. The pair
--   $$\Big(\tilde u_+^{(j)}+\tfrac{1-\mu}{\mu+1}\nabla\Phi_{k_+}(\cdot,y_j)\cdot n_0,\ \ \tilde u_-^{(j)}-\tfrac2{\mu+1}\nabla\Phi_{k_-}(\cdot,x_j)\cdot n_0\Big)$$
--   then solves the TSP with data $\tilde g_j+\hat g_j$. Here $\hat g_j$ is uniformly bounded, and $\tilde g_j$ is uniformly bounded in $BC^{0,\alpha}\times L^p$ (proof of Lemma 5.1). The argument of Theorem 5.2 produces the correction $v_j$.
--
--   **Formalization Note** This is the $H^1$ conjunct of `dipole_core_bound`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3 and its proof, PDF pp. 21-22 (first part of the proof, p. 21: reduction to data g̃ + ĝ, then as in Theorem 5.2).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_h1_core (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
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
            h1Norm D0 (fun x => (u j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
                dipoleSource km (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0) x -
                vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
