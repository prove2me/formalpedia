-- Prove2me | Theorems.Thm_RISRO_step_3_invertibility
-- name    : RISRO.step_3_invertibility
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:32:48.835516+00:00
-- url     : https://prove2.me/theorems/26fcdca6-e2a6-43dc-b360-0204d3549d5e
-- title:
--   Step 3 of Theorem 1 — (56) and invertibility of $B^{t+1}$
-- statement:
--   Let $\bar X$ be a stationary point of (1), $\bar\epsilon=y-\mathcal A(\bar X)$, let $\mathcal A$ satisfy the $2r$-RIP, and let $X^0$ satisfy (19) and $\|\mathcal A^*(\bar\epsilon)\|_F\le\frac{1-R_{2r}}{4\sqrt5}\sigma_r(\bar X)$. Consider the $t$-th iteration of RISRO with $\theta_t=\max\{\|\sin\Theta(U^t,\bar U)\|,\|\sin\Theta(V^t,\bar V)\|\}\le\frac12$ and $\|X^t-\bar X\|_F\le\|X^0-\bar X\|_F$.
--    Then every solution $(B^{t+1},D_1^{t+1},D_2^{t+1})$ of (5) satisfies, in spectral norms,
--
--   $$
--   \max\{\|B^{t+1}-\tilde B^t\|,\|D_1^{t+1}-\tilde D_1^t\|,\|D_2^{t+1}-\tilde D_2^t\|\}\le\frac3{16}\sigma_r(\bar X),
--   $$
--
--   and $\sigma_r(B^{t+1})\ge\frac9{16}\sigma_r(\bar X)>0$, so that $B^{t+1}$ is invertible.
--
--   This is the step that keeps the update of RISRO well defined along the run.
--
--   Differences from the source:
--   - generalization: the t-th iterate X^t, U^t, V^t of RISRO → any frames U, V with X = U S Vᵀ for some r×r matrix S, rank X not assumed; reason: the proof uses only this form (reading R5); every iterate of every run has it
--   - generalization: R_k defined for 1 ≤ k ≤ min(p₁, p₂) (Definition 1) → ripConst A k for every k; reason: it agrees with Definition 1 where that is defined; the paper uses R_{3r} and Lemma 8 at rank 3r, which may exceed min(p₁, p₂)
--   - encoding: (19) with the minimum of 1/4 and (1 - R_{2r})/(4√5 R_{3r}) → two inequalities, ‖X⁰ - X̄‖_F ≤ σ_r/4 and 4√5 R_{3r} ‖X⁰ - X̄‖_F ≤ (1 - R_{2r}) σ_r; reason: at R_{3r} = 0 the page reads +∞, while Lean gives x/0 = 0; the two forms agree for R_{3r} > 0
--   - encoding: ∇f(X̄)ᵀŪ = 0 and ∇f(X̄)V̄ = 0 → X̄ᵀ∇f(X̄) = 0 and ∇f(X̄)X̄ᵀ = 0 (IsRankRStationary); reason: equivalent for rank X̄ = r, because Σ̄ is invertible
--   - encoding: Ū, V̄ the singular vectors of X̄ in θ_t → any orthonormal Ū, V̄ with X̄ = Ū S̄ V̄ᵀ; reason: for rank X̄ = r they span the singular subspaces, and θ_t depends only on the subspaces
--   - encoding: rank r, r implicitly positive → explicit hypothesis 1 ≤ r; reason: σ_r is undefined at r = 0; this excludes only that undefined case
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, proof of Theorem 1, Step 3, display (56), p.39

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_sinTheta
import Definitions.Def_RISRO_IsLSMinimizer
import Definitions.Def_RISRO_IsIterate
import Definitions.Def_RISRO_IsRankRStationary

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Step 3 of the proof of Theorem 1.** Under the hypotheses of Theorem 1, given `θ_t ≤ 1/2` and
`‖X^t - X̄‖_F ≤ ‖X⁰ - X̄‖_F`, we have (56),
`max{‖B^{t+1} - B̃^t‖, ‖D₁^{t+1} - D̃₁^t‖, ‖D₂^{t+1} - D̃₂^t‖} ≤ (3/16) σ_r(X̄)`, and
`σ_r(B^{t+1}) ≥ (9/16) σ_r(X̄) > 0`, so that `B^{t+1}` is invertible.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, proof of Theorem 1, Step 3, display (56), p.39.

Formalization Notes: `θ_t = max{‖sin Θ(U^t, Ū)‖, ‖sin Θ(V^t, V̄)‖}`, display (51), p.38, where
`Ū`, `V̄` are any orthonormal matrices with `X̄ = Ū S̄ V̄ᵀ`; as `rank X̄ = r` they span the singular
subspaces of `X̄`, on which `θ_t` alone depends. The three norms in (56) are spectral. (19) is
stated multiplicatively as `h19a`, `h19b`, because `R_{3r}` may vanish. -/
theorem step_3_invertibility {p₁ p₂ n r : ℕ} (hr : 1 ≤ r) (A : Fin n → Matrix (Fin p₁) (Fin p₂) ℝ) (y : Fin n → ℝ)
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
    (hθ : max (sinTheta r U Ubar) (sinTheta r V Vbar) ≤ 1 / 2)
    (hX : frobeniusNorm (X - Xbar) ≤ frobeniusNorm (X₀ - Xbar)) :
    opNorm (B - Uᵀ * Xbar * V) ≤ 3 / 16 * sv Xbar (r - 1) ∧
      opNorm (D₁ - Ucᵀ * Xbar * V) ≤ 3 / 16 * sv Xbar (r - 1) ∧
      opNorm (D₂ - Vcᵀ * Xbarᵀ * U) ≤ 3 / 16 * sv Xbar (r - 1) ∧
      9 / 16 * sv Xbar (r - 1) ≤ sv B (r - 1) ∧
      0 < 9 / 16 * sv Xbar (r - 1) ∧
      IsUnit B.det := by sorry

end RISRO
