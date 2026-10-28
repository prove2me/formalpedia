-- Prove2me | Theorems.Thm_RobustQueueRatio_SPStability_lemma_4
-- name    : RobustQueueRatio.SPStability.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:23:59.597558+00:00
-- url     : https://prove2.me/theorems/a6e06b4b-aaf7-41cd-a19c-17aea9d83fe0
-- title:
--   Lemma 4: neighbors $\Delta_1,\Delta_2$ give proportional $k$th rows of $R_{\Delta_1},R_{\Delta_2}$ and $R_{\Delta_3}=R_{\Delta_1}(I-(1-\lambda)A)=R_{\Delta_2}(I+\lambda A)$
-- statement:
--   Fix an open multiclass network $(C,M,P,\alpha)$ with $Q=(I-P^\top)^{-1}$. Let $\Delta_1,\Delta_2$ be ratio matrices that differ only in the $k$th column, where $k$ is a station. Let $\lambda\in(0,1)$ and $\Delta_3=\lambda\Delta_1+(1-\lambda)\Delta_2$. Assume that $CMQ\Delta_i$ is invertible for $i=1,2,3$, and write $R_{\Delta_i}=(CMQ\Delta_i)^{-1}$.
--
--   Since $CMQ(\Delta_2-\Delta_1)$ has only its $k$th column nonzero, it equals $uv^\top$, where $u$ is the $k$th column of $CMQ(\Delta_2-\Delta_1)$ and $v=e_k$ is the $k$th unit vector. Then:
--
--   1. $\Delta_1,\Delta_2,\Delta_3$ are ratio-matrix neighbors;
--   2. the $k$th rows of $R_{\Delta_1}$ and $R_{\Delta_2}$ are proportional,
--   $$
--   (R_{\Delta_1})_{k\cdot}=\frac{\det(R^{-1}_{\Delta_2})}{\det(R^{-1}_{\Delta_1})}\,(R_{\Delta_2})_{k\cdot};
--   $$
--   3. the two expressions
--   $$
--   A=\frac{uv^\top R_{\Delta_1}}{1+(1-\lambda)v^\top R_{\Delta_1}u}=\frac{uv^\top R_{\Delta_2}}{1-\lambda v^\top R_{\Delta_2}u}
--   $$
--   define the same matrix;
--   4. $R_{\Delta_3}=R_{\Delta_1}(I-(1-\lambda)A)=R_{\Delta_2}(I+\lambda A)$.
--
--   This is the Sherman–Morrison step that drives the paper's analysis: moving along one column of the ratio matrix changes the reflection matrix by a rank-one update.
--
--   **Formalization Note.** The station index $k$ is `k : Fin J`, and "differ only in the $k$th column" is the hypothesis that $\Delta_1$ and $\Delta_2$ agree in every column $j\neq k$. $(R)_{k\cdot}$ is the row `R k`. $u$, $v$ and the two expressions $A_1$, $A_2$ are introduced with `let`, and $A=A_1=A_2$ is stated as the conjunct `A₁ = A₂`. Both denominators equal ratios of determinants under the hypotheses, so they are nonzero and Lean's convention $x/0=0$ is not in play. The conclusion still asserts the identities outright.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 25, Lemma 4 (with the set-up (5.1)–(5.3) on the same page)

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network
import Definitions.Def_RobustQueueRatio_SPStability_ChenS
import Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix

open Matrix

namespace RobustQueueRatio.SPStability

/-- Lemma 4 (Zhao, Gurvich & Hasenbein, arXiv:2303.17746v3, p. 25). Two ratio matrices `Δ₁, Δ₂`
that differ only in column `k` (a station), `Δ₃ = λΔ₁ + (1 − λ)Δ₂` with `λ ∈ (0, 1)`, and
`CMQΔᵢ` invertible for `i = 1, 2, 3`. With `u` the `k`th column of `CMQ(Δ₂ − Δ₁)` and `v = e_k`:
`Δ₁, Δ₂, Δ₃` are neighbors; the `k`th rows satisfy (5.6); the two expressions for `A` agree; and
`R_{Δ₃} = R_{Δ₁}(I − (1 − λ)A) = R_{Δ₂}(I + λA)`. -/
theorem lemma_4 {J K : ℕ} (N : Network J K) (Δ₁ Δ₂ : Matrix (Fin K) (Fin J) ℝ) (k : Fin J)
    (lam : ℝ) (hΔ₁ : IsRatioMatrix N Δ₁) (hΔ₂ : IsRatioMatrix N Δ₂)
    (hk : ∀ i j, j ≠ k → Δ₁ i j = Δ₂ i j) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    (h₁ : IsUnit (reflInv N Δ₁).det) (h₂ : IsUnit (reflInv N Δ₂).det)
    (h₃ : IsUnit (reflInv N (lam • Δ₁ + (1 - lam) • Δ₂)).det) :
    let Δ₃ := lam • Δ₁ + (1 - lam) • Δ₂
    let u : Fin J → ℝ := fun i => reflInv N (Δ₂ - Δ₁) i k
    let v : Fin J → ℝ := Pi.single k 1
    let A₁ := (1 + (1 - lam) * (v ⬝ᵥ (refl N Δ₁ *ᵥ u)))⁻¹ • (vecMulVec u v * refl N Δ₁)
    let A₂ := (1 - lam * (v ⬝ᵥ (refl N Δ₂ *ᵥ u)))⁻¹ • (vecMulVec u v * refl N Δ₂)
    AreNeighbors ![Δ₁, Δ₂, Δ₃] ∧
      refl N Δ₁ k = ((reflInv N Δ₂).det / (reflInv N Δ₁).det) • refl N Δ₂ k ∧
      A₁ = A₂ ∧
      refl N Δ₃ = refl N Δ₁ * (1 - (1 - lam) • A₁) ∧
      refl N Δ₃ = refl N Δ₂ * (1 + lam • A₁) := by sorry

end RobustQueueRatio.SPStability
