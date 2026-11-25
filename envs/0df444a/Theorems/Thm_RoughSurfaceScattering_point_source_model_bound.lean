-- Prove2me | Theorems.Thm_RoughSurfaceScattering_point_source_model_bound
-- name    : RoughSurfaceScattering.point_source_model_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T01:48:47.448966+00:00
-- url     : https://prove2.me/theorems/c4f4f698-ce13-5b43-abcc-e4fedc54df74
-- title:
--   Model problem in Theorem 5.2: $w_{2,j}-\frac{\mu-1}{\mu(\mu+1)}\Phi_{k_-}(\cdot,x_j)$ is bounded in $H^1(D_0)$
-- statement:
--   Under the hypotheses of Theorem 5.2, there is $\delta_0>0$ with the following property. For $0<\delta<\delta_0$ and $D_0$ as in Theorem 5.2, there exist a cutoff $\chi\in C_c^\infty(\mathbb R^2)$ with $\chi=1$ on $B_1(x_0)$ and TSP solutions $(w_{1,j},w_{2,j})$ with data $\tilde g_1=(\mu^{-1}-1)\chi\,\Phi_{k_+}(\cdot,x_j)|_\Gamma$, $\tilde g_2=0$, such that
--
--   $$\Big\|w_{2,j}-\frac{\mu-1}{\mu(\mu+1)}\,\Phi_{k_-}(\cdot,x_j)\Big\|_{H^1(D_0)}\le C\qquad(j\ge1).$$
--
--   *Proof idea (paper).* Write $w_{2,j}=\mu^{-1}(\mathcal D\varphi_j+\mathcal S\psi_j)$ with $M(\varphi_j,\psi_j)=(\tilde g_1,0)$. The densities are bounded in $L^p$ by Remark 4.4. Localizing gives that $\varphi_j-\frac{2(1-\mu)}{1+\mu}\Phi_{k_+}(\cdot,x_j)$ is bounded in $H^{1/2}(\Gamma\cap B_{R-\varepsilon_0}(x_0))$. Hence
--   $$w_{2,j}\approx\frac{2(1-\mu)}{\mu(1+\mu)}\int_{\partial D_0}\partial_{n(y)}\Phi_0(\cdot,y)\,\Phi_0(y,x_j)\,ds(y),$$
--   and by elliptic regularity the double-layer potential $2\int_{\partial D_0}\partial_n\Phi_0\,\Phi_0(y,x_j)\,ds$ equals $-\Phi_0(\cdot,x_j)$ up to an $H^1(D_0)$-bounded error. Finally $\Phi_0$ may be replaced by $\Phi_{k_-}$ (`phi_diff_h1_uniform`), and $\frac{2(1-\mu)}{\mu(1+\mu)}\cdot(-\frac12)=\frac{\mu-1}{\mu(\mu+1)}$.
--
--   **Formalization Note** Together with `point_source_reduction` this gives `point_source_core_bound`, since $\mu^{-1}+\frac{\mu-1}{\mu(\mu+1)}=\frac2{\mu+1}$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 5.2, PDF pp. 18-21 (integral-equation analysis of w_{2,j}, pp. 18-21, using Theorem 4.3, Remark 4.4 and [11, Corollaries 3.7-3.8], [41, Theorem 6.13]).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem point_source_model_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∃ χ : R2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
          (∀ x ∈ Metric.ball (gpt f s0) 1, χ x = 1) ∧
        ∃ W : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (fun s => ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) *
              Phi kp (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0))
            (fun _ => 0) (W j).1 (W j).2) ∧
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => (W j).2 x - (((μ - 1) / (μ * (μ + 1)) : ℝ) : ℂ) *
              Phi km x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
