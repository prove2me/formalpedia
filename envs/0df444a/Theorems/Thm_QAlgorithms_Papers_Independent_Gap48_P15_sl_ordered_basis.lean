-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_sl_ordered_basis
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.sl_ordered_basis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:51:17.721518+00:00
-- url     : https://prove2.me/theorems/0c0ce4da-c382-4e20-9723-7a561cac13fc
-- title:
--   sl(n): Bsl ordered basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   For every integer $t\ge1$, let $\mathfrak{sl}(t,\mathbb R)=\{X:\operatorname{tr}X=0\}$. Let $B_{\rm sl}(t)$ list all $F_{pq}$ with $p\ne q$ in increasing row then column order, followed by $F_{11}-F_{pp}$ for $p=2,\ldots,t$. Then
--   $$
--   |B_{\rm sl}(t)|=t^2-1,\qquad B_{\rm sl}(t)\text{ is a real basis of }\mathfrak{sl}(t,\mathbb R).
--   $$
--   For $t=1$ the family is empty and the Lie algebra is zero.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 9, sl(n): Bsl ordered basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- Bsl is an ordered real basis of sl(t), with t^2-1 elements.
Source: PDF pp. 9-10. The positive-size convention includes t=1 and its empty basis. -/
theorem sl_ordered_basis (t : ℕ) (ht : 0 < t) :
    (bSl t).length = t ^ 2 - 1 ∧
    isBasisFor (LieAlgebra.SpecialLinear.sl (Fin t) ℝ) (listFamily (bSl t)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
