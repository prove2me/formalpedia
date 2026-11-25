-- Prove2me | Theorems.Thm_RoughSurfaceScattering_point_source_reduction
-- name    : RoughSurfaceScattering.point_source_reduction
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T01:48:52.68668+00:00
-- url     : https://prove2.me/theorems/9b9a6b50-22ee-4c05-89b4-6a819eca4c20
-- title:
--   Reduction in Theorem 5.2: $u_-^{(j)}-\mu^{-1}\Phi_{k_-}(\cdot,x_j)-w_{2,j}$ is bounded in $H^1(D_0)$
-- statement:
--   Under the hypotheses of Theorem 5.2, there is $\delta_0>0$ with the following property. Let $0<\delta<\delta_0$, $x_j=x_0-(\delta/j)n(x_0)$, and let $D_0$ be as in Theorem 5.2. Let $\chi\in C_c^\infty(\mathbb R^2)$ equal $1$ on $B_1(x_0)$. Let $(u_+^{(j)},u_-^{(j)})$ solve the TSP with the point source $\Phi_{k_+}(\cdot,x_j)$, and let $(w_{1,j},w_{2,j})$ solve the TSP with data $\tilde g_1=(\mu^{-1}-1)\chi\,\Phi_{k_+}(\cdot,x_j)|_\Gamma$, $\tilde g_2=0$. Then
--
--   $$\big\|u_-^{(j)}-\mu^{-1}\Phi_{k_-}(\cdot,x_j)-w_{2,j}\big\|_{H^1(D_0)}\le C\qquad(j\ge1).$$
--
--   *Proof idea (paper).* By Lemma 2.4, $\Phi_{k_-}(\cdot,x_j)$ satisfies the DPRC in $D_-$. So $(u_+^{(j)},u_-^{(j)}-\mu^{-1}\Phi_{k_-}(\cdot,x_j))$ solves the TSP with data
--   $$g_{1,j}=\mu^{-1}\Phi_{k_-}-\Phi_{k_+},\qquad g_{2,j}=\partial_n\Phi_{k_-}-\partial_n\Phi_{k_+}.$$
--   Subtract $(w_{1,j},w_{2,j})$. The data $g_{1,j}-\tilde g_1=\mu^{-1}(\Phi_{k_-}-\Phi_{k_+})+(\mu^{-1}-1)(1-\chi)\Phi_{k_+}$ and $g_{2,j}$ are bounded in $BC^{1,\alpha}\times BC^{0,\alpha}$ uniformly in $j$. This uses Lemma 5.1, the Sobolev embedding, and the fact that $1-\chi=0$ near $x_j$. The stability estimate of Theorem 4.3 on the bounded set $D_0$ then gives the bound.
--
--   **Formalization Note** The data are functions of the parameter $s$ of $\Gamma$, as in `IsTSPSolution`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 5.2, PDF pp. 18-21 (first paragraph of the proof: Lemma 2.4, Remark 2.5, Lemma 5.1 and the stability part of Theorem 4.3).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem point_source_reduction (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∀ χ : R2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
          (∀ x ∈ Metric.ball (gpt f s0) 1, χ x = 1) →
        ∀ u W : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).1
            (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).2
            (u j).1 (u j).2) →
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (fun s => ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) *
              Phi kp (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0))
            (fun _ => 0) (W j).1 (W j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => (u j).2 x - ((μ⁻¹ : ℝ) : ℂ) *
              Phi km x (gpt f s0 - (δ / (j : ℝ)) • normal f s0) - (W j).2 x) ≤
              ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
