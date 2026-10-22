-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_model_rank_cartan
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.model_rank_cartan
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:56:39.86739+00:00
-- url     : https://prove2.me/theorems/5e2aabfb-4292-4b32-99e6-7035a88e1316
-- title:
--   so(4,4) plus so(2,2): rank 6 and Cartan extension examples
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   Let $L=\mathfrak{so}(4,4)\oplus\mathfrak{so}(2,2)$ in the source's block-diagonal twelve-by-twelve realization, and let $b_1,\ldots,b_{34}$ be its displayed ordered family on PDF page 16. Then
--   $$
--   \operatorname{rank}L=6,\qquad
--   (b_1,b_6,b_{34},b_{31},b_{16},b_{11})\text{ is a basis of a Cartan subalgebra of }L.
--   $$
--   This Cartan contains both starting lists $[b_1,b_6]$ and $[b_1,b_6,b_{11}]$. The second source output lists the same basis in the order $[b_1,b_6,b_{11},b_{34},b_{31},b_{16}]$.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 18, so(4,4) plus so(2,2): rank 6 and Cartan extension examples

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- The block model has rank 6 and Cartan basis [b1,b6,b34,b31,b16,b11].
Source: PDF pp. 17-18. The second run permutes this basis and adds b11 to the
starting list; the same mathematical assertion covers both runs. -/
theorem model_rank_cartan :
    LieAlgebra.rank ℝ blockModel = 6 ∧
    isCartanBasisFor blockModel ![modelBasis 0, modelBasis 5, modelBasis 33,
      modelBasis 30, modelBasis 15, modelBasis 10] := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
