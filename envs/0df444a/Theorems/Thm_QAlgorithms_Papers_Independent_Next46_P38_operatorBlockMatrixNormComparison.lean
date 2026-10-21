-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P38_operatorBlockMatrixNormComparison
-- name    : QAlgorithms.Papers.Independent.Next46.P38.operatorBlockMatrixNormComparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:41:17.36548+00:00
-- url     : https://prove2.me/theorems/f8513161-9cdb-4d3e-b5eb-2e184ef11c2b
-- title:
--   Operator block matrix norm comparison
-- statement:
--   Let $H$ be a complete complex Hilbert space, let $I$ and $J$ be finite index sets, and let $x_{ij}\in B(H)$ for $i\in I$, $j\in J$. Let $(e_i)_{i\in I}$ and $(f_j)_{j\in J}$ be families of orthogonal projections such that $e_i e_k=0$ for distinct $i,k$ and $f_j f_l=0$ for distinct $j,l$. There is no orthogonality condition between the two families. Set $a_{ij}=\|e_i x_{ij}f_j\|_{B(H)}$, and regard $A=(a_{ij})$ as a linear map from $\ell_2(J)$ to $\ell_2(I)$. Then
--
--   $$
--   \left\|\sum_{i\in I}\sum_{j\in J}e_i x_{ij}f_j\right\|_{B(H)}
--   \leq \|A\|_{B(\ell_2(J),\ell_2(I))}.
--   $$
--
--   This estimate compares a sum of operator blocks with its matrix of scalar block norms.
--
--   **Formalization Note** The rectangular scalar matrix is embedded as the upper-right block of a square matrix on $I\sqcup J$, with all other blocks zero. The right-hand side is the norm of the induced continuous linear map on Euclidean space.
-- source:
--   Noncommutative maximal ergodic theorems, arXiv:math/0505308v2, PDF p. 13, Lemma 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P38

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P38

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Lemma 3.2, PDF p.13: the norm of the sum of compressed operator blocks
is at most the Hilbert-space operator norm of their scalar norm matrix.
The row projections are pairwise orthogonal, as are the column projections;
no orthogonality across the two families is assumed. Finite rectangular
families and arbitrary complete complex Hilbert spaces are allowed. -/
theorem operatorBlockMatrixNormComparison
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (x : I → J → (H →L[ℂ] H))
    (e : I → (H →L[ℂ] H)) (f : J → (H →L[ℂ] H))
    (he : ∀ i, IsStarProjection (e i))
    (hf : ∀ j, IsStarProjection (f j))
    (heDisjoint : Pairwise (fun i k => e i * e k = 0))
    (hfDisjoint : Pairwise (fun j k => f j * f k = 0)) :
    ‖∑ i : I, ∑ j : J, e i * x i j * f j‖ ≤
      ‖Matrix.toEuclideanCLM (n := Sum I J) (𝕜 := ℂ) (blockNormPadding x e f)‖ := by sorry

end QAlgorithms.Papers.Independent.Next46.P38

end
