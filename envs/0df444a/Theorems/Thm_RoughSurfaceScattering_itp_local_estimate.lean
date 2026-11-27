-- Prove2me | Theorems.Thm_RoughSurfaceScattering_itp_local_estimate
-- name    : RoughSurfaceScattering.itp_local_estimate
-- status  : Open
-- author  : @もち
-- created : 2026-11-27T02:15:56.083969+00:00
-- url     : https://prove2.me/theorems/760f3d33-8146-49d2-9960-5f558596ef32
-- title:
--   Localized a priori estimate for the interior transmission problem ($\rho\ne1$)
-- statement:
--   Let $D_0$ be as in Theorem 6.1, with $B_{2\delta}(x_0)\cap D^-\subseteq D_0\subseteq D^-$, and let $\rho>0$, $\rho\ne1$, and $k_1,k_2\in\mathbb R$. There is $C$ with the following property. Suppose $V,W\in C^2(D_0)$, both $C^1$ up to $\Gamma$ near $x_0$, solve $\Delta V+k_1^2V=0$ and $\Delta W+k_2^2W=0$ in $D_0$, and satisfy
--   $$V=W,\qquad \rho\,\partial_nV=\partial_nW\qquad\text{on }\Gamma\cap B_{2\delta}(x_0).$$
--   Then
--   $$\|V\|_{H^1(D_0)}+\|W\|_{H^1(D_0)}\le C\big(\|V\|_{L^2(D_0)}+\|W\|_{L^2(D_0)}+\|V\|_{H^1(D_0\setminus\bar B_\delta)}+\|W\|_{H^1(D_0\setminus\bar B_\delta)}\big).$$
--
--   *Proof idea.* Multiply by a cutoff $\psi\in C_c^\infty(B_{2\delta}(x_0))$ with $\psi=1$ on $\bar B_\delta(x_0)$. Then $(\psi V,\psi W)$ solves an ITP in $D_0$ with $L^2$ sources and boundary data supported in $D_0\setminus\bar B_\delta$ resp. on $\Gamma\cap(B_{2\delta}\setminus\bar B_\delta)$. Apply the estimate (6.2) of [9, Theorem 6.7], which uses $\rho\ne1$, together with the trace theorem on $D_0\setminus\bar B_\delta$.
--
--   **Formalization Note** The trace norms of (6.2) are replaced by $H^1$ norms on $D_0\setminus\bar B_\delta$, so no trace spaces are needed.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, proof of Theorem 6.1, PDF pp. 22-24 (estimate (6.2) from [9, Theorem 6.7], localized near Γ ∩ B_{2δ}(x_0)).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem itp_local_estimate (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (lam : ℝ) (hlam : 0 < lam ∧ lam ≤ 1)
    (hf' : IsC2Lambda lam f) (s0 δ : ℝ) (hδ : 0 < δ) (D0 : Set R2) (hD0 : IsC2LambdaDomain lam D0)
    (hball : Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0) (hsub : D0 ⊆ Dminus f)
    (ρ k1 k2 : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) :
    ∃ C : ℝ, ∀ (V W : R2 → ℂ) (DV DW : R2 → (R2 →L[ℝ] ℂ)),
      ContDiffOn ℝ 2 V D0 → ContDiffOn ℝ 2 W D0 →
      IsHelmholtzOn D0 k1 V → IsHelmholtzOn D0 k2 W →
      IsC1On (closure D0 ∩ Metric.ball (gpt f s0) (2 * δ)) V DV →
      IsC1On (closure D0 ∩ Metric.ball (gpt f s0) (2 * δ)) W DW →
      (∀ s, gpt f s ∈ Metric.ball (gpt f s0) (2 * δ) → V (gpt f s) = W (gpt f s) ∧
        (ρ : ℂ) * DV (gpt f s) (normal f s) = DW (gpt f s) (normal f s)) →
      h1Norm D0 V + h1Norm D0 W ≤ ENNReal.ofReal C * (l2Norm D0 V + l2Norm D0 W +
        h1Norm (D0 \ Metric.closedBall (gpt f s0) δ) V +
        h1Norm (D0 \ Metric.closedBall (gpt f s0) δ) W) := by sorry

end RoughSurfaceScattering
