-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_sl3_first_generator_rejected
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.sl3_first_generator_rejected
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:51:50.076005+00:00
-- url     : https://prove2.me/theorems/3cb23c8e-c844-49f8-877d-0178df10ebc9
-- title:
--   sl(3): the first basis element fails the normality guard
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   In the source's ordered basis of $\mathfrak{sl}(3,\mathbb R)$ the first element is $b_1=F_{12}$. Its ordinary-transpose commutator is
--   $$
--   [b_1,b_1^{\mathsf T}]=\operatorname{diag}(1,-1,0),\qquad \neg\operatorname{Star}([b_1]).
--   $$
--   Here $\operatorname{Star}(v)$ requires $[v_i,v_j^{\mathsf T}]=0$ for every $i\le j$, including the diagonal pairs. Thus this singleton fails the mathematical input guard. This assertion concerns the guard.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 11, sl(3): the first basis element fails the normality guard

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- The first Bsl(3) matrix b1=F12 fails Star, with the exact displayed commutator.
Source: PDF pp. 10-11. This is failure of the guard, not a Cartan nonexistence claim. -/
theorem sl3_first_generator_rejected :
    ⁅((Matrix.single 1 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)), (((Matrix.single 1 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))).transpose⁆ =
      Matrix.diagonal ![(1 : ℝ), -1, 0] ∧
    ¬ star ![((Matrix.single 1 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))] := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
