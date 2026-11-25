-- Prove2me | Theorems.Thm_RoughSurfaceScattering_dipole_core_bound
-- name    : RoughSurfaceScattering.dipole_core_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T00:31:52.803903+00:00
-- url     : https://prove2.me/theorems/2fff49c1-7d4a-4c69-9a55-ea6550a39d0a
-- title:
--   Theorem 5.3 with $\Phi_{k_-}$: the dipole-source estimate for $u_-^{(j)}$
-- statement:
--   Under the hypotheses of Theorem 5.3, let $x_j=x_0-(\delta/j)n(x_0)$ and $y_j=x_0+(\delta/j)n(x_0)$. Let $(u_+^{(j)},u_-^{(j)})$ solve the TSP with the incident dipole $\nabla_x\Phi_{k_+}(x,x_j)\cdot n(x_0)$. Then, uniformly in $j$,
--
--   $$\Big\|u_-^{(j)}-\frac{2}{\mu+1}\nabla_x\Phi_{k_-}(x,x_j)\cdot n(x_0)-v_j\Big\|_{H^1(D_0)}\le C,\qquad \|v_j\|_{L^2(D_0)}\le C,$$
--
--   where $v_j$ is the correction `vCorr`. This is Theorem 5.3 with $\Phi_0$ replaced by $\Phi_{k_-}$ in the leading term; by `dipole_diff_h1_uniform` the two forms are equivalent.
--
--   **Formalization Note** The quantifier structure is that of `dipole_source_singularity`.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Theorem 5.3 and its proof, PDF pp. 21-22 (the integral-equation argument, as in Theorem 5.2).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem dipole_core_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
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
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) ≤ ENNReal.ofReal C ∧
            l2Norm D0 (vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by sorry

end RoughSurfaceScattering
