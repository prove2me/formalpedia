-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_source_singularity
-- name    : RoughSurfaceScattering.dipole_source_singularity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:58:57.961811+00:00
-- url     : https://prove2.me/theorems/00ad3444-77d2-4065-81f6-b127ef5859ff
-- title:
--   Theorem 5.3: $H^1$ singularity of the transmitted field for a hypersingular point source
-- statement:
--   Under the hypotheses and notation of Theorem 5.2 ($f\in BC^{1,1}\cap C^{2,\lambda}$, scatterer conditions, $x_0\in\Gamma$, $x_j=x_0-\frac\delta jn(x_0)$, $D_0$), there is $\delta_0>0$ such that for every $\delta\in(0,\delta_0)$ the points $y_j:=x_0+\frac\delta jn(x_0)$ lie in $D^-$ and the following holds. Let $D_0$ be a bounded $C^{2,\lambda}$ domain with $B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^-$, and let $(\tilde u_+^{(j)},\tilde u_-^{(j)})$ solve the TSP with incident hypersingular point source $\tilde u^i_j=\nabla_x\Phi_{k_+}(\cdot,x_j)\cdot n(x_0)$. With
--
--   $$v_j(x)=\frac{2\mu(1-\mu)}{(\mu+1)^2}\int_{\partial D_0}\frac{\partial\Phi_0(x,y)}{\partial n(y)}\big(\nabla_x\Phi_0(y,x_j)+\nabla_x\Phi_0(y,y_j)\big)\cdot n(x_0)\,ds(y),\quad x\in D_0,$$
--
--   there is $C$ independent of $j$ such that
--
--   $$\Big\|\tilde u_-^{(j)}-\frac2{\mu+1}\nabla_x\Phi_0(\cdot,x_j)\cdot n(x_0)-v_j\Big\|_{H^1(D_0)}\le C\quad\text{and}\quad\|v_j\|_{L^2(D_0)}\le C\qquad(j\ge1).$$
--
--   For $\mu=1$ the correction $v_j$ vanishes. This estimate is the one used in Section 6 when $\mu=1$.
--
--   **Formalization Note** $n(y)$ in $v_j$ is the outward unit normal of $D_0$ and $ds$ is arc length on $\partial D_0$ (one-dimensional Hausdorff measure). "$\delta$ small enough" is stated as the existence of a threshold $\delta_0$, and one constant $C$ serves both bounds.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, claim c007; Section 5, Theorem 5.3, PDF pp. 21-22

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_source_singularity (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      (∀ j : ℕ, 1 ≤ j → gpt f s0 + (δ / (j : ℝ)) • normal f s0 ∈ Dminus f) ∧
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∀ u : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u j).1 (u j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => (u j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
                dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0) x -
                vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) ≤ ENNReal.ofReal C ∧
            l2Norm D0 (vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
