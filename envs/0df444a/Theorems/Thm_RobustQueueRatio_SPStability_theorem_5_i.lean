-- Prove2me | Theorems.Thm_RobustQueueRatio_SPStability_theorem_5_i
-- name    : RobustQueueRatio.SPStability.theorem_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:00.799821+00:00
-- url     : https://prove2.me/theorems/83997720-ce82-41ae-8c88-81cd888c1f4d
-- title:
--   Theorem 5(i): completely-$\mathcal S$ is preserved along a segment between ratio-matrix neighbors
-- statement:
--   Fix an open multiclass network $(C,M,P,\alpha)$ with $Q=(I-P^\top)^{-1}$. Let $\Delta_1,\Delta_2$ be ratio-matrix neighbors, $\lambda\in(0,1)$ and $\Delta_3=\lambda\Delta_1+(1-\lambda)\Delta_2$. Assume that $CMQ\Delta_i$ is invertible for $i=1,2,3$, and write $R_{\Delta_i}=(CMQ\Delta_i)^{-1}$. Then $\Delta_1,\Delta_2,\Delta_3$ are ratio-matrix neighbors, and
--
--   $$
--   R_{\Delta_1},\ R_{\Delta_2}\ \text{completely-}\mathcal S\ \Longrightarrow\ R_{\Delta_3}\ \text{completely-}\mathcal S .
--   $$
--
--   This is the "orthogonal convexity" of the completely-$\mathcal S$ property: the property is not convex over all ratio matrices, but it is convex along segments parallel to one column.
--
--   **Formalization Note.** This item is part (i) of Theorem 5; part (ii) is a separate item. No hypothesis on the signs of the determinants is added: the paper's statement has none.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 13, Theorem 5(i)

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RobustQueueRatio.SPStability

/-- Theorem 5(i), orthogonal convexity of completely-S (Zhao, Gurvich & Hasenbein,
arXiv:2303.17746v3, p. 13). For ratio-matrix neighbors `Δ₁, Δ₂`, `Δ₃ = λΔ₁ + (1 − λ)Δ₂` with
`λ ∈ (0, 1)`, and `CMQΔᵢ` invertible (`i = 1, 2, 3`): `Δ₁, Δ₂, Δ₃` are neighbors, and if
`R_{Δ₁}` and `R_{Δ₂}` are completely-S, so is `R_{Δ₃}`. -/
theorem theorem_5_i {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (lam : ℝ)
    (hΔ₁ : IsRatioMatrix N Δ₁) (hΔ₂ : IsRatioMatrix N Δ₂) (hnb : AreNeighbors ![Δ₁, Δ₂])
    (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (h₁ : IsUnit (reflInv N Δ₁).det) (h₂ : IsUnit (reflInv N Δ₂).det)
    (h₃ : IsUnit (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det) :
    AreNeighbors ![Δ₁, Δ₂, lam • Δ₁ + (1 - lam) • Δ₂] ∧
      (IsCompletelyS (refl N Δ₁) → IsCompletelyS (refl N Δ₂) →
        IsCompletelyS (refl N (lam • Δ₁ + (1 - lam) • Δ₂))) := by sorry

end RobustQueueRatio.SPStability
