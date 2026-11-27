-- Prove2me | Theorems.Thm_RoughSurfaceScattering_itp_small_domain_l2
-- name    : RoughSurfaceScattering.itp_small_domain_l2
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:26:35.215362+00:00
-- url     : https://prove2.me/theorems/0e0a41da-56e0-411c-9166-d5a1dc690441
-- title:
--   $L^2$ well-posedness of the interior transmission problem in small domains ($k_1\ne k_2$)
-- statement:
--   Let $k_1,k_2>0$ with $k_1\ne k_2$. For $\delta$ small there is a bounded $C^{2,\lambda}$ domain $D_0$ with $B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^-$, and a constant $C$, such that the following holds. Suppose $V,W\in C^2(D_0)$ are $C^1$ up to $\Gamma\cap B_{2\delta}(x_0)$, solve $\Delta V+k_1^2V=0$ and $\Delta W+k_2^2W=0$ in $D_0$, and satisfy $V=W$, $\partial_nV=\partial_nW$ on $\Gamma\cap B_{2\delta}(x_0)$. Then
--   $$\|V\|_{L^2(D_0)}+\|W\|_{L^2(D_0)}\le C\big(\|V\|_{H^1(D_0\setminus\bar B_{3\delta/2})}+\|W\|_{H^1(D_0\setminus\bar B_{3\delta/2})}\big).$$
--
--   *Proof idea (paper).* $(V,W)$ solves the ITP (6.3) with Cauchy data that vanish on $\Gamma\cap B_{2\delta}$. These data are lifted by $u=(1-\chi_1)(V-W)\in H^1_\Delta(D_0)$, with $\chi_1=1$ on $B_{3\delta/2}$. Well-posedness of (6.3) in $L^2$ for small domains [10] gives $\|V\|_{L^2}+\|W\|_{L^2}\le C\|u\|_{H^1_\Delta}$. The norm $\|u\|_{H^1_\Delta}$ is controlled by the $H^1$ norms on $D_0\setminus\bar B_{3\delta/2}$, using the Helmholtz equations for $\Delta u$.
--
--   **Formalization Note** Trace norms are avoided by bounding the lifting directly.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1 (ii)-(iii), PDF pp. 24-25 (problem (6.3), 'by the classic results in [10], we can let D_0 be sufficiently small such that (6.3) is well-posed in L^2(D_0) × L^2(D_0)').

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem itp_small_domain_l2 (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1)
    (hf' : IsC2Lambda lam f) (s0 k1 k2 : ℝ) (hk1 : 0 < k1) (hk2 : 0 < k2) (hk : k1 ≠ k2) :
    ∃ δ1 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ1 →
      ∃ D0 : Set R2, IsC2LambdaDomain lam D0 ∧
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 ∧ D0 ⊆ Dminus f ∧
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
