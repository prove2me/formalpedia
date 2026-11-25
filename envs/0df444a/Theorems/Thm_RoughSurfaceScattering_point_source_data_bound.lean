-- Prove2me | Theorems.Thm_RoughSurfaceScattering_point_source_data_bound
-- name    : RoughSurfaceScattering.point_source_data_bound
-- status  : Open
-- author  : @もち
-- created : 2026-11-25T06:40:17.207348+00:00
-- url     : https://prove2.me/theorems/f3d6bc45-eb4c-40a7-8118-47fdeea27d65
-- title:
--   Uniform Hölder bounds for the reduced TSP data in Theorem 5.2
-- statement:
--   Under the hypotheses of Theorem 5.2, for $\delta$ small, a cutoff $\chi\in C_c^\infty$ with $\chi=1$ on $B_1(x_0)$, and $0<\alpha<1$, consider the combined data
--   $$G_1=-\Phi_{k_+}(\cdot,x_j)-(\mu^{-1}-1)\chi\,\Phi_{k_+}(\cdot,x_j)+\mu^{-1}\Phi_{k_-}(\cdot,x_j)=\mu^{-1}(\Phi_{k_-}-\Phi_{k_+})(\cdot,x_j)+(\mu^{-1}-1)(1-\chi)\Phi_{k_+}(\cdot,x_j),$$
--   $$G_2=\partial_n(\Phi_{k_-}-\Phi_{k_+})(\cdot,x_j)\quad\text{on }\Gamma .$$
--   Then $G_1\in BC^{1,\alpha}(\Gamma)$ and $G_2\in BC^{0,\alpha}(\Gamma)$, with $\|G_1\|_{1,\alpha,\Gamma}+\|G_2\|_{0,\alpha,\Gamma}\le C$ uniformly in $j$.
--
--   The difference $\Phi_{k_-}-\Phi_{k_+}$ is $W^{2,p}$ and hence $C^{1,\alpha}$ near the source, uniformly in the source point (Lemma 5.1). The factor $1-\chi$ vanishes near $x_j$, and the Hankel functions decay at infinity.
--
--   **Formalization Note** The data are written exactly in the form `g - h - k` used by `tsp_stability_h1`, for the incident point source, the model solution and $(0,\mu^{-1}\Phi_{k_-}(\cdot,x_j))$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 5.2 (p. 18): 'By the regularity derived in Lemma 5.1, the Sobolev embedding and the decay property of the Hankel functions at infinity'.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem point_source_data_bound (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      ∀ χ : R2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        (∀ x ∈ Metric.ball (gpt f s0) 1, χ x = 1) →
      ∀ α : ℝ, 0 < α → α < 1 →
      ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
        IsBC1AlphaGam f α (fun s =>
          (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) *
            Phi kp (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0) -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0))) ∧
        IsBC0AlphaGam f α (fun s =>
          (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).2 s - 0 -
          -((μ : ℂ) * (((μ⁻¹ : ℝ) : ℂ) * fderiv ℝ
            (fun x => Phi km x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) (gpt f s) (normal f s)))) ∧
        holderNorm1 f α (fun s =>
          (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).1 s -
          ((μ⁻¹ - 1 : ℝ) : ℂ) * (χ (gpt f s) : ℂ) *
            Phi kp (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0) -
          -(((μ⁻¹ : ℝ) : ℂ) * Phi km (gpt f s) (gpt f s0 - (δ / (j : ℝ)) • normal f s0))) +
        holderNorm0 f α (fun s =>
          (incData f (pointSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0))).2 s - 0 -
          -((μ : ℂ) * (((μ⁻¹ : ℝ) : ℂ) * fderiv ℝ
            (fun x => Phi km x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) (gpt f s) (normal f s))))
          ≤ C := by sorry

end RoughSurfaceScattering
