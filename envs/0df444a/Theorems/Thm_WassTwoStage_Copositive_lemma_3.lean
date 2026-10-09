-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_lemma_3
-- name    : WassTwoStage.Copositive.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:58:36.50202+00:00
-- url     : https://prove2.me/theorems/d375cb8a-9b94-4d5a-8e9a-58b0db57115c
-- title:
--   Lemma 3 — complete recourse implies $WW^\top \succ_{\mathcal C} 0$
-- statement:
--   If problem (1) has complete recourse, i.e. there is $y^+ \in \mathbb R^{N_2}$ with $Wy^+ > 0$ componentwise, then the $M\times M$ matrix $WW^\top$ is strictly copositive:
--   $$\lambda^\top WW^\top\lambda > 0 \qquad \text{for all } \lambda\in\mathbb R^M_+,\ \lambda\neq 0.$$
--
--   Lemma 3 supplies the strict copositivity needed for the Slater point in the proof of Theorem 4.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 15, Lemma 3

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

open Matrix

namespace WassTwoStage.Copositive

/-- Lemma 3, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 15: if problem (1) has complete recourse
(some `y⁺` with `Wy⁺ > 0`), then `WWᵀ ≻_C 0`, i.e. `λᵀWWᵀλ > 0` for every nonzero `λ ∈ ℝ^M_+`. -/
theorem lemma_3 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (hCR : d.CompleteRecourse) :
    StrictlyCopositive (d.W * d.Wᵀ) := by sorry

end WassTwoStage.Copositive
