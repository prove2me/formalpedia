-- Prove2me | Theorems.Thm_RISRO_step_4_contraction_chain
-- name    : RISRO.step_4_contraction_chain
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:34:56.106786+00:00
-- url     : https://prove2.me/theorems/0ddf3581-2fc1-4f77-9749-a4b986397af9
-- title:
--   Step 4 of Theorem 1 — the contraction chain
-- statement:
--   Let $\bar X$ be a stationary point of (1), $\bar\epsilon=y-\mathcal A(\bar X)$, let $\mathcal A$ satisfy the $2r$-RIP, and let $X^0$ satisfy (19) and $\|\mathcal A^*(\bar\epsilon)\|_F\le\frac{1-R_{2r}}{4\sqrt5}\sigma_r(\bar X)$. Consider the $t$-th iteration of RISRO with $\theta_t=\max\{\|\sin\Theta(U^t,\bar U)\|,\|\sin\Theta(V^t,\bar V)\|\}\le\frac12$ and $\|X^t-\bar X\|_F\le\|X^0-\bar X\|_F$.
--    Let $(B,D_1,D_2)$ be a solution of (5), $\rho=\max\{\|D_1B^{-1}\|,\|B^{-1}D_2^\top\|\}$, $X^{t+1}=X_UB^{-1}X_V^\top$. Then
--
--   $$
--   1+3\Bigl(\rho\vee\frac{\theta_t}{\sqrt{1-\theta_t^2}}\vee\frac{\theta_t\rho}{\sqrt{1-\theta_t^2}}\Bigr)^2\le5,
--   $$
--
--   and
--
--   $$
--   \begin{aligned}
--   \|X^{t+1}-\bar X\|_F^2&\le5\bigl\|(\mathcal L_t^*\mathcal A^*\mathcal A\mathcal L_t)^{-1}\mathcal L_t^*\mathcal A^*\epsilon^t\bigr\|_F^2\\
--   &\le\frac{5\|X^t-\bar X\|^2}{(1-R_{2r})^2\sigma_r^2(\bar X)}\Bigl(R_{3r}^2\|X^t-\bar X\|_F^2+4\|\mathcal A^*(\bar\epsilon)\|_F^2+4R_{3r}\|\mathcal A^*(\bar\epsilon)\|_F\|X^t-\bar X\|_F\Bigr)\\
--   &\le\frac9{16}\|X^t-\bar X\|_F^2 .
--   \end{aligned}
--   $$
--
--   This is the induction step of Theorem 1, and its last line gives the factor $3/4$.
--
--   **Formalization Note.** $B^{-1}$ is the true inverse, because $B$ is invertible under these hypotheses by Step 3.
--
--   Differences from the source:
--   - generalization: the t-th iterate X^t, U^t, V^t of RISRO → any frames U, V with X = U S Vᵀ for some r×r matrix S, rank X not assumed; reason: the proof uses only this form (reading R5); every iterate of every run has it
--   - generalization: R_k defined for 1 ≤ k ≤ min(p₁, p₂) (Definition 1) → ripConst A k for every k; reason: it agrees with Definition 1 where that is defined; the paper uses R_{3r} and Lemma 8 at rank 3r, which may exceed min(p₁, p₂)
--   - encoding: (19) with the minimum of 1/4 and (1 - R_{2r})/(4√5 R_{3r}) → two inequalities, ‖X⁰ - X̄‖_F ≤ σ_r/4 and 4√5 R_{3r} ‖X⁰ - X̄‖_F ≤ (1 - R_{2r}) σ_r; reason: at R_{3r} = 0 the page reads +∞, while Lean gives x/0 = 0; the two forms agree for R_{3r} > 0
--   - encoding: ∇f(X̄)ᵀŪ = 0 and ∇f(X̄)V̄ = 0 → X̄ᵀ∇f(X̄) = 0 and ∇f(X̄)X̄ᵀ = 0 (IsRankRStationary); reason: equivalent for rank X̄ = r, because Σ̄ is invertible
--   - encoding: Ū, V̄ the singular vectors of X̄ in θ_t → any orthonormal Ū, V̄ with X̄ = Ū S̄ V̄ᵀ; reason: for rank X̄ = r they span the singular subspaces, and θ_t depends only on the subspaces
--   - encoding: (L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t → the w with normalOp w = L_t^* A^* ϵ^t (IsErrorTriple); reason: the operator is injective here, so w is unique and equals the page's expression
--   - encoding: matrices M ∈ Ran(L_t^*) with a zero bottom-right block → triples (W₀, W₁, W₂) with tripleNorm; reason: the same space with the same norm
--   - generalization: the induction hypotheses of p.38 include that B̃^t is invertible → no such hypothesis; reason: it follows from θ_t ≤ 1/2 by (53)-(54), so the hypothesis excludes nothing
--   - encoding: rank r, r implicitly positive → explicit hypothesis 1 ≤ r; reason: σ_r is undefined at r = 0; this excludes only that undefined case
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, proof of Theorem 1, Step 4, p.40

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_Triple
import Definitions.Def_RISRO_tripleNorm
import Definitions.Def_RISRO_sinTheta
import Definitions.Def_RISRO_IsErrorTriple
import Definitions.Def_RISRO_IsLSMinimizer
import Definitions.Def_RISRO_IsIterate
import Definitions.Def_RISRO_IsRankRStationary

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Step 4 of the proof of Theorem 1: the contraction chain.** Under the hypotheses of Theorem 1,
given `θ_t ≤ 1/2` and `‖X^t - X̄‖_F ≤ ‖X⁰ - X̄‖_F`, we have
`1 + 3 (ρ_{t+1} ∨ θ_t/√(1-θ_t²) ∨ θ_t ρ_{t+1}/√(1-θ_t²))² ≤ 5`, and thus
`‖X^{t+1} - X̄‖_F² ≤ 5 ‖(L_t^* A^* A L_t)⁻¹ L_t^* A^* ϵ^t‖_F²
 ≤ 5 ‖X^t - X̄‖² / ((1 - R_{2r})² σ_r²(X̄)) · (R_{3r}² ‖X^t - X̄‖_F² + 4 ‖A^*(ϵ̄)‖_F²
   + 4 R_{3r} ‖A^*(ϵ̄)‖_F ‖X^t - X̄‖_F)
 ≤ (9/16) ‖X^t - X̄‖_F²`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, proof of Theorem 1, Step 4, p.40.

Formalization Notes: `ρ_{t+1} = max{‖D₁ B⁻¹‖, ‖B⁻¹ D₂ᵀ‖}`, display (57), p.39, in spectral norms.
`X^{t+1} = X_U B⁻¹ X_Vᵀ`. Here `B⁻¹` is the true inverse because `B` is
invertible under these hypotheses (`step_3_invertibility`). The chain is the one printed on p.40,
with `(1 - R_{2r})²`; display (52), p.38, prints `(1 - R_{2r}²)`. See `step_3_invertibility` for
`θ_t` and for (19). The page also lists "`B̃^t` is invertible" among the induction hypotheses; it is
not a hypothesis here because it follows from `θ_t ≤ 1/2`, see (53)–(54). -/
theorem step_4_contraction_chain {p₁ p₂ n r : ℕ} (hr : 1 ≤ r) (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
    (Xbar X₀ X : Matrix (Fin p₁) (Fin p₂) ℝ)
    (Ubar : Matrix (Fin p₁) (Fin r) ℝ) (Vbar : Matrix (Fin p₂) (Fin r) ℝ)
    (Sbar : Matrix (Fin r) (Fin r) ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (D₁ : Matrix (Fin (p₁ - r)) (Fin r) ℝ)
    (D₂ : Matrix (Fin (p₂ - r)) (Fin r) ℝ)
    (hstat : IsRankRStationary A y r Xbar)
    (hRIP : ripConst A (2 * r) < 1)
    (h19a : frobeniusNorm (X₀ - Xbar) ≤ 1 / 4 * sv Xbar (r - 1))
    (h19b : 4 * √5 * ripConst A (3 * r) * frobeniusNorm (X₀ - Xbar) ≤
      (1 - ripConst A (2 * r)) * sv Xbar (r - 1))
    (hres : frobeniusNorm (observationOpAdjoint A (y - observationOp A Xbar)) ≤
      (1 - ripConst A (2 * r)) / (4 * √5) * sv Xbar (r - 1))
    (hUbar : Ubarᵀ * Ubar = 1) (hVbar : Vbarᵀ * Vbar = 1) (hXbar : Xbar = Ubar * Sbar * Vbarᵀ)
    (hIter : IsIterate U Uc V Vc X)
    (hLS : IsLSMinimizer A y U Uc V Vc B D₁ D₂)
    (θ ρ : ℝ) (hθdef : θ = max (sinTheta r U Ubar) (sinTheta r V Vbar))
    (hρdef : ρ = max (opNorm (D₁ * B⁻¹)) (opNorm (B⁻¹ * D₂ᵀ)))
    (hθ : θ ≤ 1 / 2)
    (hX : frobeniusNorm (X - Xbar) ≤ frobeniusNorm (X₀ - Xbar))
    (w : Triple p₁ p₂ r) (hw : IsErrorTriple A y Xbar U Uc V Vc w) :
    1 + 3 * max ρ (max (θ / √(1 - θ ^ 2)) (θ * ρ / √(1 - θ ^ 2))) ^ 2 ≤ 5 ∧
      frobeniusNorm ((U * B + Uc * D₁) * B⁻¹ * (V * Bᵀ + Vc * D₂)ᵀ - Xbar) ^ 2 ≤
        5 * tripleNorm w ^ 2 ∧
      5 * tripleNorm w ^ 2 ≤
        5 * opNorm (X - Xbar) ^ 2 / ((1 - ripConst A (2 * r)) ^ 2 * sv Xbar (r - 1) ^ 2) *
          (ripConst A (3 * r) ^ 2 * frobeniusNorm (X - Xbar) ^ 2 +
            4 * frobeniusNorm (observationOpAdjoint A (y - observationOp A Xbar)) ^ 2 +
            4 * ripConst A (3 * r) * frobeniusNorm (observationOpAdjoint A (y - observationOp A Xbar)) * frobeniusNorm (X - Xbar)) ∧
      5 * opNorm (X - Xbar) ^ 2 / ((1 - ripConst A (2 * r)) ^ 2 * sv Xbar (r - 1) ^ 2) *
          (ripConst A (3 * r) ^ 2 * frobeniusNorm (X - Xbar) ^ 2 +
            4 * frobeniusNorm (observationOpAdjoint A (y - observationOp A Xbar)) ^ 2 +
            4 * ripConst A (3 * r) * frobeniusNorm (observationOpAdjoint A (y - observationOp A Xbar)) * frobeniusNorm (X - Xbar)) ≤
        9 / 16 * frobeniusNorm (X - Xbar) ^ 2 := by sorry

end RISRO
