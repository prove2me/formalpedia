-- Prove2me | Theorems.Thm_RISRO_lemma_7_schur_perturbation
-- name    : RISRO.lemma_7_schur_perturbation
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:30:54.935137+00:00
-- url     : https://prove2.me/theorems/85e07672-ee8d-44b9-901e-daf84c70f817
-- title:
--   Lemma 7 — perturbation of $FG^{-1}H$ (Zhang et al., Lemma 3)
-- statement:
--   Let $F,\hat F\in\mathbb R^{p_1\times r}$, $G,\hat G\in\mathbb R^{r\times r}$, $H,\hat H\in\mathbb R^{r\times p_2}$. If $G$ and $\hat G$ are invertible, $\|FG^{-1}\|\le\lambda_1$ and $\|\hat G^{-1}\hat H\|\le\lambda_2$ in spectral norm, then
--
--   $$
--   \bigl\|\hat F\hat G^{-1}\hat H-FG^{-1}H\bigr\|_F\le\lambda_2\|\hat F-F\|_F+\lambda_1\|\hat H-H\|_F+\lambda_1\lambda_2\|\hat G-G\|_F .
--   $$
--
--   In the proof of Theorem 1 this bounds the Schur-complement term $\Delta^{t+1}$ of (60).
--
--   Differences from the source: none.
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, Lemma 7, display (86), p.49

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Lemma 7 (Zhang et al., 2020, Lemma 3).** For `F, F̂ ∈ ℝ^{p₁×r}`, `G, Ĝ ∈ ℝ^{r×r}`,
`H, Ĥ ∈ ℝ^{r×p₂}` with `G`, `Ĝ` invertible, `‖F G⁻¹‖ ≤ λ₁` and `‖Ĝ⁻¹ Ĥ‖ ≤ λ₂`, we have (86):
`‖F̂ Ĝ⁻¹ Ĥ - F G⁻¹ H‖_F ≤ λ₂ ‖F̂ - F‖_F + λ₁ ‖Ĥ - H‖_F + λ₁ λ₂ ‖Ĝ - G‖_F`.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, Lemma 7, display (86), p.49.

Formalization Note: the hypotheses use the spectral norm `opNorm`, the conclusion the Frobenius
norm. `⁻¹` is the true inverse, as `G` and `Ĝ` are assumed invertible. -/
theorem lemma_7_schur_perturbation {p₁ p₂ r : ℕ}
    (F Fh : Matrix (Fin p₁) (Fin r) ℝ) (G Gh : Matrix (Fin r) (Fin r) ℝ)
    (H Hh : Matrix (Fin r) (Fin p₂) ℝ) (l₁ l₂ : ℝ)
    (hG : IsUnit G.det) (hGh : IsUnit Gh.det)
    (h₁ : opNorm (F * G⁻¹) ≤ l₁) (h₂ : opNorm (Gh⁻¹ * Hh) ≤ l₂) :
    frobeniusNorm (Fh * Gh⁻¹ * Hh - F * G⁻¹ * H) ≤
      l₂ * frobeniusNorm (Fh - F) + l₁ * frobeniusNorm (Hh - H) +
        l₁ * l₂ * frobeniusNorm (Gh - G) := by sorry

end RISRO
