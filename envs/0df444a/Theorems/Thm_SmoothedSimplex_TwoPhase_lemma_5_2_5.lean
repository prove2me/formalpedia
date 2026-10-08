-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_2_5
-- name    : SmoothedSimplex.TwoPhase.lemma_5_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:29:20.714482+00:00
-- url     : https://prove2.me/theorems/b7f9298b-f6a8-4da3-8179-6bec051cb96a
-- title:
--   Lemma 5.2.5 (Approximation of α by α̃)
-- statement:
--   For $d\ge3$, let $A,\widetilde A$ be square real matrices close in both relative directions in Euclidean operator norm: $\|I-\widetilde A^{-1}A\|,\|I-A^{-1}\widetilde A\|\le\varepsilon\le9/(17d^2)$. Let $\mathcal F\ge0$ be measurable and invariant under positive scaling. For $\delta=1/d^2$,
--   $$\mathbb E_{\alpha\in A_\delta}\mathcal F(A\alpha)\le6\,\mathbb E_{\widetilde\alpha\in A_0}\mathcal F(\widetilde A\widetilde\alpha).$$
--   This compares the random directions of two nearby simplices. The expectations are extended nonnegative integrals so no integrability assumption hides an infinite case.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.2.5, printed p. 74, PDF p. 74

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.2.5 (Approximation of α by α̃), printed p. 74, PDF p. 74. The matrix norm is the Euclidean operator norm, and F is explicitly measurable. Formalization Note: `[n]` is `Fin n`; all expectations use the specified probability laws. -/
theorem lemma_5_2_5 {d : ℕ} (hd : 3 ≤ d)
    (A B : Matrix (Fin d) (Fin d) ℝ) (F : Point d → ℝ)
    (hF : Measurable F) (hFnonneg : ∀ x, 0 ≤ F x)
    (hFdir : ∀ x : Point d, ∀ c : ℝ, 0 < c → F (c • x) = F x)
    (ε : ℝ)
    (hAB : ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (1 - B⁻¹ * A)‖ ≤ ε)
    (hBA : ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (1 - A⁻¹ * B)‖ ≤ ε)
    (hε : ε ≤ 9 / (17 * (d : ℝ)^2)) :
    (∫⁻ α, ENNReal.ofReal (F ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A (WithLp.toLp 2 α)))
      ∂(simplexLaw d (1 / (d : ℝ)^2))) ≤
      (6 : ENNReal) * (∫⁻ α, ENNReal.ofReal
        (F ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) B (WithLp.toLp 2 α))) ∂(simplexLaw d 0)) := by sorry

end SmoothedSimplex.TwoPhase
