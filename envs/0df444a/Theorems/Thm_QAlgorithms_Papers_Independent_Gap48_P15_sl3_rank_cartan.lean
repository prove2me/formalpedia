-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_sl3_rank_cartan
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.sl3_rank_cartan
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:52:27.828768+00:00
-- url     : https://prove2.me/theorems/f2a3c140-fd0c-4cfd-a12b-8922da2a86f7
-- title:
--   sl(3): rank 2 and diagonal Cartan basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   Let $L=\mathfrak{sl}(3,\mathbb R)$ and let $b_7=F_{11}-F_{22}$ and $b_8=F_{11}-F_{33}$, as in the displayed source computation. Then
--   $$
--   \operatorname{rank}L=2,\qquad (b_7,b_8)\text{ is a basis of a Cartan subalgebra of }L.
--   $$
--   The resulting Cartan is the trace-zero diagonal subalgebra and retains the displayed starting element $b_7$.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 11, sl(3): rank 2 and diagonal Cartan basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- sl(3) has rank 2 and Cartan basis [b7,b8].
Source: PDF p. 11. The displayed input and matrices use b7; the preceding prose
says b8. We follow the input/output formulas, without correcting the general routine. -/
theorem sl3_rank_cartan :
    LieAlgebra.rank ℝ (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ) = 2 ∧
    isCartanBasisFor (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ)
      ![((Matrix.single 1 1 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)) - ((Matrix.single 2 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)),
        ((Matrix.single 1 1 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)) - ((Matrix.single 3 3 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))] := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
