-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P15_splitG2_basis
-- name    : QAlgorithms.Papers.Independent.Gap48.P15.splitG2_basis
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:54:58.390381+00:00
-- url     : https://prove2.me/theorems/2df8afcc-61ad-47f1-8bac-bf0aafaa86ee
-- title:
--   split g2: the displayed 14-matrix basis
-- statement:
--   All matrices and spans are over $\mathbb R$, and the Lie bracket is $[X,Y]=XY-YX$. The source uses one-based matrix indices. Write $F_{pq}$ for the matrix unit, $J_{pq}=F_{pq}-F_{qp}$ and $Z_{pq}=F_{pq}+F_{qp}$. Here rank means Lie rank, and a Cartan subalgebra means a nilpotent, self-normalizing Lie subalgebra.
--
--   Let $b_1,\ldots,b_{14}$ be exactly the eight-by-eight matrices in BSplitg2 on PDF page 14, and let $L$ be their generated real matrix Lie algebra. Explicitly,
--   $$
--   \begin{aligned}
--   b={}&(J_{23}-J_{76},-J_{42}+J_{68},Z_{25}+Z_{47},Z_{26}-Z_{48},
--   Z_{27}-Z_{45},Z_{28}+Z_{46},J_{34}+J_{78},Z_{35}-Z_{46},\\
--   &Z_{36}+Z_{45},Z_{37}-Z_{48},Z_{38}+Z_{47},-J_{65}-J_{78},
--   J_{57}+J_{68},J_{58}+J_{76}).
--   \end{aligned}
--   $$
--   Then
--   $$
--   b\text{ is linearly independent over }\mathbb R,\qquad
--   \operatorname{span}_{\mathbb R}\{b_i\}=L.
--   $$
--   This basis assertion includes bracket closure of the span and preserves the distinct split real matrix realization.
--
--   The explicit family is asserted to be linearly independent and to span the indicated subalgebra; these properties are conclusions. This records the mathematical assertion accompanying the source output.
-- source:
--   Algorithm to compute the rank and a Cartan subalgebra of a matrix Lie algebra with Mathematica, arXiv:math/0205235v1, PDF p. 14, split g2: the displayed 14-matrix basis

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

namespace QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

/-- The 14 literal split g2 generators are independent and span their generated
Lie algebra. Source: PDF pp. 14-15, BSplitg2. Its real form is kept distinct. -/
theorem splitG2_basis : isBasisFor splitG2 bSplitG2 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P15
