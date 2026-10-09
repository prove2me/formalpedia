-- Prove2me | Theorems.Thm_TinyCoreset_Affine_lemma18_orthogonal_translation
-- name    : TinyCoreset.Affine.lemma18_orthogonal_translation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:16.936928+00:00
-- url     : https://prove2.me/theorems/5509fc56-13a3-4867-be3f-a8992dbd98c6
-- title:
--   Lemma 18, p. 616 — for centred M and t ⊥ L, dist²(M, t + L) = dist²(M, L) + n‖t‖²
-- statement:
--   Let $M\in\mathbb R^{n\times d}$ have mean row $\mu(M)=\vec 0$. Let $j\in[1,d-1]$ be an integer and let $L$ be a $j$-dimensional linear subspace of $\mathbb R^d$. Let $t\in L^\perp$ and let $C=t+L$ be the translation of $L$ by $t$. Then
--
--   $$\operatorname{dist}^2(M,C)=\operatorname{dist}^2(M,L)+n\cdot\|t\|^2.$$
--
--   For centred data, moving a subspace orthogonally by $t$ raises the cost by exactly $n\|t\|^2$, independently of the data. This is what lets a mean-zero coreset with the right total weight transfer its guarantee from linear to affine subspaces.
--
--   **Formalization Note** The paper says "$L$ be an affine $j$-dimensional subspace"; the lemma uses $L^\perp$ and is applied in the proof of Theorem 19 only to linear $L$, so $L$ is a linear subspace (`Submodule`) here. $C$ is `AffineSubspace.mk' t L`. For $n=0$ both sides are $0$.
-- source:
--   Feldman, Schmidt & Sohler, Turning Big Data into Tiny Data, SIAM J. Comput. 49(3) (2020), p. 616, Lemma 18; proof pp. 616–617

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_Affine_Setting

namespace TinyCoreset.Affine

/-- Lemma 18, p. 616. Let `M ∈ ℝ^{n×d}` have mean row `µ(M) = 0`, let `j ∈ [1, d − 1]`, let `L` be a
`j`-dimensional linear subspace of `ℝ^d` (the page says "affine"; the lemma uses `L^⊥` and is applied
to linear `L`), let `t ∈ L^⊥` and `C = t + L`. Then `dist²(M, C) = dist²(M, L) + n · ‖t‖²`. -/
theorem lemma18_orthogonal_translation {n d : ℕ} (M : Matrix (Fin n) (Fin d) ℝ)
    (hM : mean M = 0) (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hL : Module.finrank ℝ L = j)
    (t : EuclideanSpace ℝ (Fin d)) (ht : t ∈ Lᗮ) :
    TinyCoreset.DimRed.distSq M (AffineSubspace.mk' t L : Set (EuclideanSpace ℝ (Fin d))) =
      TinyCoreset.DimRed.distSq M (L : Set (EuclideanSpace ℝ (Fin d))) + (n : ℝ) * ‖t‖ ^ 2 := by sorry

end TinyCoreset.Affine
