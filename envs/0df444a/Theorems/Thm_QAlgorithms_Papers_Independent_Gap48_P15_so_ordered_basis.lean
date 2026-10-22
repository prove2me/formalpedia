-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_so_ordered_basis
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.so_ordered_basis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:48:53.984996+00:00
-- url     : https://prove2.me/theorems/1403ce96-22bd-4c9b-af1b-8af104d58c45
-- title:
--   so(n): BSo ordered basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   For every integer $t\ge1$, let $\mathfrak{so}(t,\mathbb R)=\{X:X^{\mathsf T}=-X\}$. Enumerate $J_{pq}$ by increasing $p=1,\ldots,t-1$ and then increasing $q=p+1,\ldots,t$, obtaining the ordered family $B_{\rm So}(t)$. Then
--
--   $$
--   |B_{\rm So}(t)|=\frac{t(t-1)}2,\qquad B_{\rm So}(t)\text{ is a real basis of }\mathfrak{so}(t,\mathbb R).
--   $$
--
--   For $t=1$ this is the empty basis of the zero Lie algebra.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 5, so(n): BSo ordered basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- BSo is an ordered real basis of so(t), including its stated cardinality.
Source: PDF p. 5, BSo. The positive-size convention includes t=1 and its empty basis. -/
theorem so_ordered_basis (t : ℕ) (ht : 0 < t) :
    (bSo t).length = t * (t - 1) / 2 ∧
    isBasisFor (LieAlgebra.Orthogonal.so (Fin t) ℝ) (listFamily (bSo t)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
