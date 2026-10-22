-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_so9_rank_cartan
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.so9_rank_cartan
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:49:53.56248+00:00
-- url     : https://prove2.me/theorems/96cbb4d4-0587-4f0b-8738-5def3d005d4d
-- title:
--   so(9): rank 4 and the displayed Cartan basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   For $L=\mathfrak{so}(9,\mathbb R)$, put $v=(b_1,b_{36},b_{31},b_{22})=(J_{12},J_{89},J_{67},J_{45})$. Then
--
--   $$
--   \operatorname{rank}L=4,\qquad v\text{ is a basis of a Cartan subalgebra of }L.
--   $$
--
--   In particular, the Cartan retains the starting element $b_1$.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 7, so(9): rank 4 and the displayed Cartan basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- so(9) has rank 4 and Cartan basis [b1,b36,b31,b22].
Source: PDF p. 7, RankOfSo[9,{b1}]. -/
theorem so9_rank_cartan :
    LieAlgebra.rank ℝ (LieAlgebra.Orthogonal.so (Fin 9) ℝ) = 4 ∧
    isCartanBasisFor (LieAlgebra.Orthogonal.so (Fin 9) ℝ)
      ![J 9 1 2, J 9 8 9, J 9 6 7, J 9 4 5] := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
