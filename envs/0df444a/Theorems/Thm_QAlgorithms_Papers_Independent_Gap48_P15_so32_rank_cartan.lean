-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_so32_rank_cartan
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.so32_rank_cartan
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:50:35.133411+00:00
-- url     : https://prove2.me/theorems/0ea2f9fc-4a0c-408a-bc17-33e9c9f8fd41
-- title:
--   so(32): rank 16 and the displayed Cartan basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   Let $L=\mathfrak{so}(32,\mathbb R)$. In the BSo ordering the source output is
--   $$
--   v=(b_1,b_{496},b_{491},b_{482},b_{469},b_{452},b_{431},b_{406},b_{377},b_{344},b_{307},b_{266},b_{221},b_{172},b_{119},b_{62})
--   =(J_{12},J_{31,32},J_{29,30},J_{27,28},J_{25,26},J_{23,24},J_{21,22},J_{19,20},J_{17,18},J_{15,16},J_{13,14},J_{11,12},J_{9,10},J_{7,8},J_{5,6},J_{3,4}).
--   $$
--   Then
--   $$
--   \dim_{\mathbb R}L=496,\qquad \operatorname{rank}L=16,\qquad v\text{ is a basis of a Cartan subalgebra of }L.
--   $$
--   The initial element $b_1$ is retained.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 9, so(32): rank 16 and the displayed Cartan basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- so(32) has rank 16, dimension 496, and the displayed Cartan basis.
Source: PDF pp. 8-9, in the output order b1,b496,b491,...,b62. -/
theorem so32_rank_cartan :
    LieAlgebra.rank ℝ (LieAlgebra.Orthogonal.so (Fin 32) ℝ) = 16 ∧
    Module.finrank ℝ (LieAlgebra.Orthogonal.so (Fin 32) ℝ) = 496 ∧
    isCartanBasisFor (LieAlgebra.Orthogonal.so (Fin 32) ℝ)
      ![J 32 1 2, J 32 31 32, J 32 29 30, J 32 27 28,
        J 32 25 26, J 32 23 24, J 32 21 22, J 32 19 20,
        J 32 17 18, J 32 15 16, J 32 13 14, J 32 11 12,
        J 32 9 10, J 32 7 8, J 32 5 6, J 32 3 4] := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
