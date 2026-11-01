-- Prove2me | Theorems.Thm_RISRO_display_50_error_bound
-- name    : RISRO.display_50_error_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:34:40.884032+00:00
-- url     : https://prove2.me/theorems/a1a6e066-6461-43d3-9380-bfd115902592
-- title:
--   Display (50) — the error bound at a stationary point
-- statement:
--   Let $\bar X$ be a rank $r$ stationary point of problem (1), $\bar\epsilon=y-\mathcal A(\bar X)$, and suppose $\mathcal A$ satisfies the $2r$-RIP. Then at the $t$-th iteration of RISRO
--
--   $$
--   \|\mathcal L_t^*\mathcal A^*(\bar\epsilon)\|_F^2\le\frac{4\|X^t-\bar X\|^2}{\sigma_r^2(\bar X)}\|\mathcal A^*(\bar\epsilon)\|_F^2,
--   $$
--
--   and consequently
--
--   $$
--   \bigl\|(\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t)^{-1}\mathcal L_t^*\mathcal A^*\epsilon^t\bigr\|_F^2\le\frac{\|X^t-\bar X\|^2}{(1-R_{2r})^2\sigma_r^2(\bar X)}\Bigl(R_{3r}^2\|X^t-\bar X\|_F^2+4\|\mathcal A^*(\bar\epsilon)\|_F^2+4R_{3r}\|\mathcal A^*(\bar\epsilon)\|_F\|X^t-\bar X\|_F\Bigr).
--   $$
--
--   Stationarity is what makes the residual term second order. Here $\|\cdot\|$ is the spectral norm.
--
--   Differences from the source:
--   - generalization: the t-th iterate X^t, U^t, V^t of RISRO → any frames U, V with X = U S Vᵀ for some r×r matrix S, rank X not assumed; reason: the proof uses only this form (reading R5); every iterate of every run has it
--   - generalization: R_k defined for 1 ≤ k ≤ min(p₁, p₂) (Definition 1) → ripConst A k for every k; reason: it agrees with Definition 1 where that is defined; the paper uses R_{3r} and Lemma 8 at rank 3r, which may exceed min(p₁, p₂)
--   - encoding: ∇f(X̄)ᵀŪ = 0 and ∇f(X̄)V̄ = 0 → X̄ᵀ∇f(X̄) = 0 and ∇f(X̄)X̄ᵀ = 0 (IsRankRStationary); reason: equivalent for rank X̄ = r, because Σ̄ is invertible
--   - encoding: (L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t → the w with normalOp w = L_t^* A^* ϵ^t (IsErrorTriple); reason: the operator is injective here, so w is unique and equals the page's expression
--   - encoding: matrices M ∈ Ran(L_t^*) with a zero bottom-right block → triples (W₀, W₁, W₂) with tripleNorm; reason: the same space with the same norm
--   - encoding: rank r, r implicitly positive → explicit hypothesis 1 ≤ r; reason: σ_r is undefined at r = 0; this excludes only that undefined case
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, proof of Theorem 1, Step 1, display (50), p.38

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_Triple
import Definitions.Def_RISRO_tripleNorm
import Definitions.Def_RISRO_LopAdj
import Definitions.Def_RISRO_IsErrorTriple
import Definitions.Def_RISRO_IsIterate
import Definitions.Def_RISRO_IsRankRStationary

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Step 1 of the proof of Theorem 1.** At a rank `r` stationary point `X̄`,
`‖L_t^* A^*(ϵ̄)‖_F² ≤ 4 ‖X^t - X̄‖² ‖A^*(ϵ̄)‖_F² / σ_r²(X̄)`, and hence (50):
`‖(L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t‖_F² ≤ ‖X^t - X̄‖² / ((1 - R_{2r})² σ_r²(X̄))
 · (R_{3r}² ‖X^t - X̄‖_F² + 4 ‖A^*(ϵ̄)‖_F² + 4 R_{3r} ‖A^*(ϵ̄)‖_F ‖X^t - X̄‖_F)`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, proof of Theorem 1, Step 1, display (50), p.38.

Formalization Notes: the first inequality is the squared form of p.38 (Remark 7, p.12, omits the
square on the left, a misprint). `ϵ̄ = y - A(X̄)`; `‖·‖` is `opNorm`. See
`proposition_1_iteration_error` for `IsIterate` and `w`. -/
theorem display_50_error_bound {p₁ p₂ n r : ℕ} (hr : 1 ≤ r) (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (Xbar X : Matrix (Fin p₁) (Fin p₂) ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (hstat : IsRankRStationary A y r Xbar) (hRIP : ripConst A (2 * r) < 1)
    (hIter : IsIterate U Uc V Vc X)
    (w : Triple p₁ p₂ r) (hw : IsErrorTriple A y Xbar U Uc V Vc w) :
    tripleNorm (LopAdj U Uc V Vc (observationOpAdjoint A (y - observationOp A Xbar))) ^ 2 ≤
        4 * opNorm (X - Xbar) ^ 2 / sv Xbar (r - 1) ^ 2 *
          frobeniusNorm (observationOpAdjoint A (y - observationOp A Xbar)) ^ 2 ∧
      tripleNorm w ^ 2 ≤
        opNorm (X - Xbar) ^ 2 / ((1 - ripConst A (2 * r)) ^ 2 * sv Xbar (r - 1) ^ 2) *
        (ripConst A (3 * r) ^ 2 * frobeniusNorm (X - Xbar) ^ 2 +
          4 * frobeniusNorm (observationOpAdjoint A (y - observationOp A Xbar)) ^ 2 +
          4 * ripConst A (3 * r) * frobeniusNorm (observationOpAdjoint A (y - observationOp A Xbar)) * frobeniusNorm (X - Xbar)) := by sorry

end RISRO
