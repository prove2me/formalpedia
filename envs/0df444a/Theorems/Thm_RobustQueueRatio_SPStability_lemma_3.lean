-- Prove2me | Theorems.Thm_RobustQueueRatio_SPStability_lemma_3
-- name    : RobustQueueRatio.SPStability.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:11.873827+00:00
-- url     : https://prove2.me/theorems/01da7cb3-f72f-4913-bbdd-748d61d2fa41
-- title:
--   Lemma 3: if $\det(CMQ\Delta_1)$, $\det(CMQ\Delta_2)$ share a sign, then $CMQ\Delta_3$ is invertible for neighbors
-- statement:
--   Fix an open multiclass network $(C,M,P,\alpha)$ with $Q=(I-P^\top)^{-1}$. Let $\Delta_1,\Delta_2$ be ratio-matrix neighbors, $\lambda\in(0,1)$ and $\Delta_3=\lambda\Delta_1+(1-\lambda)\Delta_2$. Then $\Delta_1,\Delta_2,\Delta_3$ are ratio-matrix neighbors. Moreover, suppose that $R^{-1}_{\Delta_1}=CMQ\Delta_1$ and $R^{-1}_{\Delta_2}=CMQ\Delta_2$ are invertible and that
--
--   $$
--   \det(R^{-1}_{\Delta_1})\cdot\det(R^{-1}_{\Delta_2})>0 .
--   $$
--
--   Then $R^{-1}_{\Delta_3}=CMQ\Delta_3$ is invertible.
--
--   This is the step that keeps the reflection matrix well defined in the interior of the set of ratio matrices, given that it is well defined at the corners with determinants of a common sign.
--
--   **Formalization Note.** "Have the same sign" is the strict inequality $\det(CMQ\Delta_1)\det(CMQ\Delta_2)>0$, which is meaningful because both determinants are nonzero. Invertibility is `IsUnit` of the determinant.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 14, Lemma 3

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RobustQueueRatio.SPStability

/-- Lemma 3 (Zhao, Gurvich & Hasenbein, arXiv:2303.17746v3, p. 14). For ratio-matrix neighbors
`Δ₁, Δ₂` and `Δ₃ = λΔ₁ + (1 − λ)Δ₂` with `λ ∈ (0, 1)`: `Δ₁, Δ₂, Δ₃` are neighbors, and if
`CMQΔ₁`, `CMQΔ₂` are invertible with determinants of the same sign, then `CMQΔ₃` is invertible. -/
theorem lemma_3 {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (lam : ℝ)
    (hΔ₁ : IsRatioMatrix N Δ₁) (hΔ₂ : IsRatioMatrix N Δ₂) (hnb : AreNeighbors ![Δ₁, Δ₂])
    (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (h₁ : IsUnit (reflInv N Δ₁).det) (h₂ : IsUnit (reflInv N Δ₂).det)
    (hsign : 0 < (reflInv N Δ₁).det * (reflInv N Δ₂).det) :
    AreNeighbors ![Δ₁, Δ₂, lam • Δ₁ + (1 - lam) • Δ₂] ∧
      IsUnit (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det := by sorry

end RobustQueueRatio.SPStability
