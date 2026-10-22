-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_so6_rank_cartan
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.so6_rank_cartan
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:49:23.408173+00:00
-- url     : https://prove2.me/theorems/f93f2cb9-28de-45cc-8d59-36fae376da60
-- title:
--   so(6): rank 3 and the displayed Cartan basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   For $L=\mathfrak{so}(6,\mathbb R)$, put $v=(J_{12},J_{34},J_{56})=(b_1,b_{10},b_{15})$. Then
--
--   $$
--   \operatorname{rank} L=3,\qquad v\text{ is a basis of a Cartan subalgebra of }L.
--   $$
--
--   This Cartan contains both starting lists $[b_1]$ and $[b_1,b_{10}]$. The two source output orders describe the same subalgebra.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 6, so(6): rank 3 and the displayed Cartan basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- so(6) has rank 3 and Cartan basis [b1,b10,b15]=[J12,J34,J56].
Source: PDF pp. 6-7; the two execution orders yield the same displayed basis. -/
theorem so6_rank_cartan :
    LieAlgebra.rank ℝ (LieAlgebra.Orthogonal.so (Fin 6) ℝ) = 3 ∧
    isCartanBasisFor (LieAlgebra.Orthogonal.so (Fin 6) ℝ)
      ![J 6 1 2, J 6 3 4, J 6 5 6] := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
