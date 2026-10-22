-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_sl5_rank_cartan
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.sl5_rank_cartan
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:52:55.51525+00:00
-- url     : https://prove2.me/theorems/e736e0a0-a710-4c0d-adc6-f021131c0f65
-- title:
--   sl(5): rank 4 and extension of two given diagonal elements
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   Let $L=\mathfrak{sl}(5,\mathbb R)$ and set $d_p=F_{11}-F_{pp}$ for $p=2,3,4,5$. The source labels these $b_{21},b_{22},b_{23},b_{24}$ respectively. Then
--   $$
--   \operatorname{rank}L=4,\qquad
--   \left(d_2,d_3,d_4-d_5,-\frac23d_2-\frac23d_3+d_4+d_5\right)
--   \text{ is a basis of a Cartan subalgebra of }L.
--   $$
--   This basis extends the two given elements $b_{21}$ and $b_{22}$, with both coefficients equal to $-2/3$ in the final vector.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 12, sl(5): rank 4 and extension of two given diagonal elements

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- sl(5) has rank 4 and the displayed Cartan basis extending [b21,b22].
Source: PDF pp. 11-12. Both rational coefficients in the last vector are -2/3. -/
theorem sl5_rank_cartan :
    let d : Fin 4 → (Matrix (Fin 5) (Fin 5) ℝ) :=
      fun i => ((Matrix.single 1 1 (1 : ℝ)).submatrix
      (fun i : Fin 5 => i.val + 1) (fun j : Fin 5 => j.val + 1)) - ((Matrix.single (i.val + 2) (i.val + 2) (1 : ℝ)).submatrix
      (fun i : Fin 5 => i.val + 1) (fun j : Fin 5 => j.val + 1))
    LieAlgebra.rank ℝ (LieAlgebra.SpecialLinear.sl (Fin 5) ℝ) = 4 ∧
    isCartanBasisFor (LieAlgebra.SpecialLinear.sl (Fin 5) ℝ)
      ![d 0, d 1, d 2 - d 3,
        (-(2 : ℝ) / 3) • d 0 + (-(2 : ℝ) / 3) • d 1 + d 2 + d 3] := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
