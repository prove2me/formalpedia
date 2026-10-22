-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_compactG2_basis
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.compactG2_basis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:53:30.865521+00:00
-- url     : https://prove2.me/theorems/e3c312b1-efe0-4da7-aa89-90bc31e0ab4f
-- title:
--   compact g2: the displayed 14-matrix basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   Let $b_1,\ldots,b_{14}$ be exactly the eight-by-eight matrices in Bg2 on PDF page 12, and let $L$ be their generated real matrix Lie algebra. Explicitly, the ordered family is
--   $$
--   \begin{aligned}
--   b={}&(J_{23}+J_{67},J_{24}+J_{68},J_{25}+J_{74},J_{26}+J_{84},
--   J_{27}+J_{45},J_{28}+J_{46},J_{34}+J_{78},J_{35}+J_{46},\\
--   &J_{36}+J_{54},J_{37}+J_{84},J_{38}+J_{47},J_{56}+J_{78},
--   J_{57}+J_{86},J_{58}+J_{67}).
--   \end{aligned}
--   $$
--   Then
--   $$
--   b\text{ is linearly independent over }\mathbb R,\qquad
--   \operatorname{span}_{\mathbb R}\{b_i\}=L.
--   $$
--   This establishes the displayed matrix realization's basis and closure. The ambient eight-dimensional representation, including its zero first row and column, is retained.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 12, compact g2: the displayed 14-matrix basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- The 14 literal compact g2 generators are linearly independent and span their
Lie-generated algebra over the reals. Source: PDF pp. 12-13, Bg2.
In particular, closure of the linear span is asserted, not assumed. -/
theorem compactG2_basis : isBasisFor compactG2 bG2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
