-- Prove2me | Theorems.Thm_RoughSurfaceScattering_itp_small_domain_l2_local
-- name    : RoughSurfaceScattering.itp_small_domain_l2_local
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:48:55.369289+00:00
-- url     : https://prove2.me/theorems/103707b1-846e-5bb3-86b9-7b13667872d7
-- title:
--   $L^2$ well-posedness of the ITP ($\rho=1$, $k_1\ne k_2$) in small domains inside $B_{3\delta}$
-- statement:
--   Same as `itp_small_domain_l2`, with the domain additionally localized: $D_0\subseteq B_{3\delta}(x_0)$. For $k_1\ne k_2$ and $\delta$ small, there is a $C^{2,\lambda}$ domain with $B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^-\cap B_{3\delta}(x_0)$ and a constant $C$ such that Helmholtz solutions $V$ ($k_1$) and $W$ ($k_2$) with equal Cauchy data on $\Gamma\cap B_{2\delta}$ satisfy
--   $$\|V\|_{L^2(D_0)}+\|W\|_{L^2(D_0)}\le C\big(\|V\|_{H^1(D_0\setminus\bar B_{3\delta/2})}+\|W\|_{H^1(D_0\setminus\bar B_{3\delta/2})}\big).$$
--   The ITP is well-posed for small domains (the eigenvalues blow up as the domain shrinks) [10]. The zero data on $\Gamma\cap B_{2\delta}$ are lifted by a cutoff supported away from $B_{3\delta/2}$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, case Γ1 ≠ Γ2 with μ1 = 1 (hypersingular sources), PDF pp. 22-24 (problem (6.3) is well-posed in L^2(D_0)×L^2(D_0) for D_0 small, [10]).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem itp_small_domain_l2_local (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (lam : ℝ)
    (hlam : 0 < lam ∧ lam ≤ 1) (hf' : IsC2Lambda lam f) (s0 k1 k2 : ℝ) (hk1 : 0 < k1) (hk2 : 0 < k2)
    (hk : k1 ≠ k2) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f ∧
        D0 ⊆ Metric.ball (gpt f s0) (3 * δ) ∧
        ∃ C : ℝ, ∀ (V W : R2 → ℂ) (DV DW : R2 → (R2 →L[ℝ] ℂ)),
          ContDiffOn ℝ 2 V D0 → ContDiffOn ℝ 2 W D0 →
          IsHelmholtzOn D0 k1 V → IsHelmholtzOn D0 k2 W →
          IsC1On (closure D0 ∩ Metric.ball (gpt f s0) (2 * δ)) V DV →
          IsC1On (closure D0 ∩ Metric.ball (gpt f s0) (2 * δ)) W DW →
          (∀ s, gpt f s ∈ Metric.ball (gpt f s0) (2 * δ) → V (gpt f s) = W (gpt f s) ∧
            DV (gpt f s) (normal f s) = DW (gpt f s) (normal f s)) →
          l2Norm D0 V + l2Norm D0 W ≤ ENNReal.ofReal C *
            (h1Norm (D0 \ Metric.closedBall (gpt f s0) (3 * δ / 2)) V +
              h1Norm (D0 \ Metric.closedBall (gpt f s0) (3 * δ / 2)) W) := by sorry

end RoughSurfaceScattering
