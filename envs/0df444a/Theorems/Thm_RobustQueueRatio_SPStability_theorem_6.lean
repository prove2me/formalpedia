-- Prove2me | Theorems.Thm_RobustQueueRatio_SPStability_theorem_6
-- name    : RobustQueueRatio.SPStability.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:02.759592+00:00
-- url     : https://prove2.me/theorems/a48b8c8f-73f6-4e1d-a793-016037c3c386
-- title:
--   Theorem 6: $R_{\Delta_3}=\beta R_{\Delta_1}+(1-\beta)R_{\Delta_2}$ for neighbors, $\beta=\lambda\det R_{\Delta_2}/(\lambda\det R_{\Delta_2}+(1-\lambda)\det R_{\Delta_1})$
-- statement:
--   Fix an open multiclass network $(C,M,P,\alpha)$ with $Q=(I-P^\top)^{-1}$. Let $\Delta_1,\Delta_2$ be ratio-matrix neighbors, $\lambda\in(0,1)$ and $\Delta_3=\lambda\Delta_1+(1-\lambda)\Delta_2$. Assume that $CMQ\Delta_i$ is invertible for $i=1,2,3$, and write $R_{\Delta_i}=(CMQ\Delta_i)^{-1}$. Then $\Delta_1,\Delta_2,\Delta_3$ are ratio-matrix neighbors, and $R_{\Delta_3}$ is a linear combination of $R_{\Delta_1}$ and $R_{\Delta_2}$:
--
--   $$
--   R_{\Delta_3}=\beta R_{\Delta_1}+(1-\beta)R_{\Delta_2},\qquad \beta=\frac{\lambda\det(R_{\Delta_2})}{\lambda\det(R_{\Delta_2})+(1-\lambda)\det(R_{\Delta_1})},
--   $$
--
--   or equivalently
--
--   $$
--   \frac{R_{\Delta_3}}{\det(R_{\Delta_3})}=\lambda\frac{R_{\Delta_1}}{\det(R_{\Delta_1})}+(1-\lambda)\frac{R_{\Delta_2}}{\det(R_{\Delta_2})}.
--   $$
--
--   Moreover, if $\det(R_{\Delta_1})$ and $\det(R_{\Delta_2})$ have the same sign, then $\beta\in(0,1)$.
--
--   The theorem says that along a segment in one column of the ratio matrix, the reflection matrix moves along a segment, reparametrized by $\beta$. Completely-$\mathcal S$ and Chen-$\mathcal S$ are then transferred along the segment in Theorem 5.
--
--   **Formalization Note.** The paper asserts $\beta\in(0,1)$ under invertibility alone. That is false when $\det(R_{\Delta_1})$ and $\det(R_{\Delta_2})$ have opposite signs: then $\beta<0$ or $\beta>1$ for every admissible $\lambda$. Such pairs occur, for example, at two neighboring static-priority corners of the paper's balanced Lu–Kumar network with $m_2+m_4>1$. The membership $\beta\in(0,1)$ is therefore stated under the added hypothesis $\det(R_{\Delta_1})\det(R_{\Delta_2})>0$; the two identities are stated without it. Under the invertibility hypotheses the denominator of $\beta$ equals $\det(R_{\Delta_1})\det(R_{\Delta_2})/\det(R_{\Delta_3})\neq 0$, so no division by zero occurs.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 14, Theorem 6

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RobustQueueRatio.SPStability

/-- Theorem 6 (Zhao, Gurvich & Hasenbein, arXiv:2303.17746v3, p. 14). For ratio-matrix neighbors
`Δ₁, Δ₂`, `Δ₃ = λΔ₁ + (1 − λ)Δ₂` with `λ ∈ (0, 1)`, and `CMQΔᵢ` invertible (`i = 1, 2, 3`):
`Δ₁, Δ₂, Δ₃` are neighbors, `R_{Δ₃} = βR_{Δ₁} + (1 − β)R_{Δ₂}` with
`β = λ det R_{Δ₂} / (λ det R_{Δ₂} + (1 − λ) det R_{Δ₁})`, equivalently
`R_{Δ₃}/det R_{Δ₃} = λ R_{Δ₁}/det R_{Δ₁} + (1 − λ) R_{Δ₂}/det R_{Δ₂}`.

**Deviation.** The page also asserts `β ∈ (0, 1)` under these hypotheses only; that is false when
`det R_{Δ₁}` and `det R_{Δ₂}` have opposite signs. Here `β ∈ (0, 1)` is concluded under the added
hypothesis `0 < det R_{Δ₁} · det R_{Δ₂}`. -/
theorem theorem_6 {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (lam : ℝ)
    (hΔ₁ : IsRatioMatrix N Δ₁) (hΔ₂ : IsRatioMatrix N Δ₂) (hnb : AreNeighbors ![Δ₁, Δ₂])
    (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (h₁ : IsUnit (reflInv N Δ₁).det) (h₂ : IsUnit (reflInv N Δ₂).det)
    (h₃ : IsUnit (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det) :
    let Δ₃ := lam • Δ₁ + (1 - lam) • Δ₂
    let β := lam * (refl N Δ₂).det / (lam * (refl N Δ₂).det + (1 - lam) * (refl N Δ₁).det)
    AreNeighbors ![Δ₁, Δ₂, Δ₃] ∧
      refl N Δ₃ = β • refl N Δ₁ + (1 - β) • refl N Δ₂ ∧
      ((refl N Δ₃).det)⁻¹ • refl N Δ₃ =
        lam • (((refl N Δ₁).det)⁻¹ • refl N Δ₁) +
          (1 - lam) • (((refl N Δ₂).det)⁻¹ • refl N Δ₂) ∧
      (0 < (refl N Δ₁).det * (refl N Δ₂).det → 0 < β ∧ β < 1) := by sorry

end RobustQueueRatio.SPStability
