-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_lemma_6
-- name    : RankOneBimatrix.BinSearch.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:03.99687+00:00
-- url     : https://prove2.me/theorems/49f36cd0-ad87-40df-8e72-d3c4dacb9899
-- title:
--   Lemma 6, p. 7 — rank reduction with λ = xᵀa
-- statement:
--   For mixed $x,y$ and any $\lambda$, conditions (b) and (c) of Lemma 6 are equivalent. When $\lambda=x^\top a$, condition (a) is equivalent to them as well.
--
--   $$(A,C+ab^\top),\qquad(A,C+\mathbf1\lambda b^\top),\qquad(A-\mathbf1\lambda b^\top,C+\mathbf1\lambda b^\top).$$
--
--   This is the rank-reduction step. **Formalization Note** The printed implication (a) to (b) is false for arbitrary fixed $\lambda$; its proof uses $\lambda=x^\top a$. The equivalence of (b) and (c) is unconditional.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 7, Lemma 6 and (7)

import Definitions.Def_RankOneBimatrix_BinSearch_Setting

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Lemma 6, p. 7. The printed (a)⇒(b) needs `λ = xᵀa`, as its proof uses;
the equivalence of (b) and (c) holds for every `λ`. -/
theorem lemma_6 {m n : ℕ} (A C : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (a : Fin m → ℝ) (b : Fin n → ℝ)
    (lam : ℝ) (hx : x ∈ Mixed m) (hy : y ∈ Mixed n) :
    (x ⬝ᵥ a = lam →
      (IsNE A (C + vecMulVec a b) x y ↔
        IsNE A (C + onesLam lam b) x y ∧ x ⬝ᵥ a = lam)) ∧
    (IsNE A (C + onesLam lam b) x y ∧ x ⬝ᵥ a = lam ↔
      IsNE (A - onesLam lam b) (C + onesLam lam b) x y ∧
        x ⬝ᵥ a = lam) := by sorry

end RankOneBimatrix.BinSearch
