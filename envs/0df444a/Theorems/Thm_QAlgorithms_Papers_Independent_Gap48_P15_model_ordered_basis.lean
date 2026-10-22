-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_model_ordered_basis
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.model_ordered_basis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:56:01.726799+00:00
-- url     : https://prove2.me/theorems/c016560d-b9e1-492e-85a0-4e196fc838c5
-- title:
--   so(4,4) plus so(2,2): displayed 34-matrix basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   Let $Q_8=\operatorname{diag}(1,1,1,1,-1,-1,-1,-1)$ and $Q_4=\operatorname{diag}(1,1,-1,-1)$. Define the source's block model by
--   $$
--   L=\left\{\operatorname{diag}(A,B):A^{\mathsf T}Q_8+Q_8A=0,\ B^{\mathsf T}Q_4+Q_4B=0\right\}\subseteq M_{12}(\mathbb R).
--   $$
--   Let $b$ be the ordered family
--   $$
--   \begin{aligned}
--   (&Z_{15},Z_{16},Z_{17},Z_{18},Z_{25},Z_{26},Z_{27},Z_{28},Z_{35},Z_{36},Z_{37},Z_{38},Z_{45},Z_{46},Z_{47},Z_{48},\\
--   &J_{12},J_{13},J_{14},J_{23},J_{24},J_{34},J_{56},J_{57},J_{58},J_{67},J_{68},J_{78},J_{9,10},J_{11,12},Z_{9,11},Z_{9,12},Z_{10,11},Z_{10,12}).
--   \end{aligned}
--   $$
--   Then
--   $$
--   b\text{ is a real basis of }L=\mathfrak{so}(4,4)\oplus\mathfrak{so}(2,2).
--   $$
--   The two cross-block rectangles vanish throughout this model.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 16, so(4,4) plus so(2,2): displayed 34-matrix basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- The literal 34-matrix family is a real basis of the block model so(4,4) plus
so(2,2). Source: PDF pp. 16-17. Both cross-block rectangles are excluded. -/
theorem model_ordered_basis : isBasisFor blockModel modelBasis := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
