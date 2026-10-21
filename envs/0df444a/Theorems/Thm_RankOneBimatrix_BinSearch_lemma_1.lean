-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_lemma_1
-- name    : RankOneBimatrix.BinSearch.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:27.107731+00:00
-- url     : https://prove2.me/theorems/7818d30c-2807-4dba-8557-172f948b530d
-- title:
--   Lemma 1, p. 5 — support conditions characterize best responses
-- statement:
--   For $x\in X$ and $y\in Y$, a player best responds exactly when every supported pure strategy attains that player's largest pure-strategy payoff. When both players satisfy the conditions, the comparison values are their unique equilibrium payoffs.
--
--   $$x_i>0\Rightarrow (Ay)_i=u,\quad (Ay)_i\le u;\qquad y_j>0\Rightarrow(B^\top x)_j=v,\quad(B^\top x)_j\le v.$$
--
--   This connects best responses to the later LP optimality conditions.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 5, Lemma 1

import Definitions.Def_RankOneBimatrix_BinSearch_Game

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Lemma 1, p. 5: support and payoff inequalities characterize best responses. -/
theorem lemma_1 {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (IsRowBR A x y ↔
      x ∈ Mixed m ∧ y ∈ Mixed n ∧ ∃ u : ℝ,
        (∀ i, (A *ᵥ y) i ≤ u) ∧
        (∀ i, x i = 0 ∨ (A *ᵥ y) i = u)) ∧
    (IsColBR B x y ↔
      x ∈ Mixed m ∧ y ∈ Mixed n ∧ ∃ v : ℝ,
        (∀ j, (B.transpose *ᵥ x) j ≤ v) ∧
        (∀ j, y j = 0 ∨ (B.transpose *ᵥ x) j = v)) ∧
    (∀ u v : ℝ,
      x ∈ Mixed m → y ∈ Mixed n →
      (∀ i, (A *ᵥ y) i ≤ u) →
      (∀ i, x i = 0 ∨ (A *ᵥ y) i = u) →
      (∀ j, (B.transpose *ᵥ x) j ≤ v) →
      (∀ j, y j = 0 ∨ (B.transpose *ᵥ x) j = v) →
      u = x ⬝ᵥ (A *ᵥ y) ∧ v = x ⬝ᵥ (B *ᵥ y)) := by sorry

end RankOneBimatrix.BinSearch
