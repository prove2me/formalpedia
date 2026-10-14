-- Prove2me | Theorems.Thm_RobustQueueRatio_SPStability_theorem_5_ii
-- name    : RobustQueueRatio.SPStability.theorem_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:20.016756+00:00
-- url     : https://prove2.me/theorems/0ceeccae-446c-4bc1-bf3d-91647146d86f
-- title:
--   Theorem 5(ii): Chen-$\mathcal S$ of $(R_\Delta,\theta_\Delta)$ is preserved along a segment between ratio-matrix neighbors
-- statement:
--   Fix an open multiclass network $(C,M,P,\alpha)$ with $Q=(I-P^\top)^{-1}$ and traffic intensities $\rho=CMQ\alpha$. Let $\Delta_1,\Delta_2$ be ratio-matrix neighbors, $\lambda\in(0,1)$ and $\Delta_3=\lambda\Delta_1+(1-\lambda)\Delta_2$. Assume that $CMQ\Delta_i$ is invertible for $i=1,2,3$. Write $R_{\Delta_i}=(CMQ\Delta_i)^{-1}$ and $\theta_{\Delta_i}=R_{\Delta_i}(\rho-e)$. Then $\Delta_1,\Delta_2,\Delta_3$ are ratio-matrix neighbors, and
--
--   $$
--   (R_{\Delta_1},\theta_{\Delta_1}),\ (R_{\Delta_2},\theta_{\Delta_2})\ \text{Chen-}\mathcal S\ \Longrightarrow\ (R_{\Delta_3},\theta_{\Delta_3})\ \text{Chen-}\mathcal S .
--   $$
--
--   This is the orthogonal convexity of the Chen-$\mathcal S$ property, the sufficient condition for stability of the Skorohod problem. Together with Lemma 3 it lets the property propagate from the static-priority corners into the whole set of ratio matrices.
--
--   **Formalization Note.** This item is part (ii) of Theorem 5; part (i) is a separate item. The drifts $\theta_{\Delta_i}$ are computed from $\Delta_i$ and the fixed network, not free vectors. No hypothesis on the signs of the determinants is added.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 13, Theorem 5(ii)

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RobustQueueRatio.SPStability

/-- Theorem 5(ii), orthogonal convexity of Chen-S (Zhao, Gurvich & Hasenbein,
arXiv:2303.17746v3, p. 13). For ratio-matrix neighbors `Δ₁, Δ₂`, `Δ₃ = λΔ₁ + (1 − λ)Δ₂` with
`λ ∈ (0, 1)`, and `CMQΔᵢ` invertible (`i = 1, 2, 3`): `Δ₁, Δ₂, Δ₃` are neighbors, and if
`(R_{Δ₁}, θ_{Δ₁})` and `(R_{Δ₂}, θ_{Δ₂})` are Chen-S, so is `(R_{Δ₃}, θ_{Δ₃})`, where
`θ_Δ = R_Δ(ρ − e)`. -/
theorem theorem_5_ii {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (lam : ℝ)
    (hΔ₁ : IsRatioMatrix N Δ₁) (hΔ₂ : IsRatioMatrix N Δ₂) (hnb : AreNeighbors ![Δ₁, Δ₂])
    (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (h₁ : IsUnit (reflInv N Δ₁).det) (h₂ : IsUnit (reflInv N Δ₂).det)
    (h₃ : IsUnit (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det) :
    AreNeighbors ![Δ₁, Δ₂, lam • Δ₁ + (1 - lam) • Δ₂] ∧
      (IsChenS (refl N Δ₁) (theta N Δ₁) → IsChenS (refl N Δ₂) (theta N Δ₂) →
        IsChenS (refl N (lam • Δ₁ + (1 - lam) • Δ₂)) (theta N (lam • Δ₁ + (1 - lam) • Δ₂))) := by sorry

end RobustQueueRatio.SPStability
