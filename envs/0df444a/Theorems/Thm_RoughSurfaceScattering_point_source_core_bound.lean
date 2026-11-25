-- Prove2me | Theorems.Thm_RoughSurfaceScattering_point_source_core_bound
-- name    : RoughSurfaceScattering.point_source_core_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T00:16:46.929946+00:00
-- url     : https://prove2.me/theorems/612055b3-8bcf-4eee-a758-eee7fc4aef5e
-- title:
--   Theorem 5.2 with $\Phi_{k_-}$: $u_-^{(j)}-\frac2{\mu+1}\Phi_{k_-}(\cdot,x_j)$ is bounded in $H^1(D_0)$
-- statement:
--   Under the hypotheses of Theorem 5.2, there is $\delta_0>0$ with the following property. Let $0<\delta<\delta_0$, $x_j=x_0-(\delta/j)\,n(x_0)$, and let $D_0$ be a bounded $C^{2,\lambda}$ domain with $B_{2\delta}(x_0)\cap D_-\subseteq D_0\subseteq D_-$. Let $(u_+^{(j)},u_-^{(j)})$ solve the TSP with the incident point source $\Phi_{k_+}(\cdot,x_j)$. Then
--
--   $$\Big\|u_-^{(j)}-\frac{2}{\mu+1}\,\Phi_{k_-}(\cdot,x_j)\Big\|_{H^1(D_0)}\le C\qquad(j\ge1),$$
--
--   with $C$ independent of $j$.
--
--   This is Theorem 5.2 with $\Phi_0$ replaced by $\Phi_{k_-}$; by `phi_diff_h1_uniform` the two forms are equivalent. The proof in the paper goes through four steps:
--   1. Reduce to the TSP with data $g_1=(\mu^{-1}-1)\chi\,\Phi_{k_+}(\cdot,x_j)$, $g_2=0$, using Theorem 4.3 and Lemma 5.1.
--   2. Represent the solution by layer potentials $\mu^{-1}(\mathcal D\varphi_j+\mathcal S\psi_j)$, with $\varphi_j,\psi_j$ bounded in $L^p$ (Remark 4.4).
--   3. Localize near $x_0$ and show that $\varphi_j-\frac{2(1-\mu)}{1+\mu}\Phi_{k_+}(\cdot,x_j)$ is bounded in $H^{1/2}$.
--   4. Apply elliptic regularity to the double-layer potential of $\Phi_0(\cdot,x_j)$ over $\partial D_0$.
--
--   **Formalization Note** $H^1$ is the platform's `h1Norm`. The quantifier structure is that of `point_source_singularity`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.2 and its proof, PDF pp. 17-21 (the whole integral-equation argument, which uses Theorem 4.3 and Remark 4.4).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem point_source_core_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∀ u : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).1
            (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).2
            (u j).1 (u j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => (u j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
              Phi km x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
