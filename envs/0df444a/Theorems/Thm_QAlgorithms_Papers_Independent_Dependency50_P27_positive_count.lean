-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_positive_count
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.positive_count
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:56:53.627984+00:00
-- url     : https://prove2.me/theorems/15fc4d4a-0970-4375-8dd6-900664babd9c
-- title:
--   §5.3.3, inversion and positive count
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Let $M=\left(\begin{smallmatrix}1&1&1\\-1&1&1\\0&0&1\end{smallmatrix}\right)$ and let $t,c$ be the query and sign-count row vectors in the orders $(Q,Q^2,1)$ and $(1,-1,0)$, respectively. Then
--
--   $$\det M=2,\qquad c=tM^{-1},\qquad c_1=\frac{\operatorname{TaQ}(z,Q)+\operatorname{TaQ}(z,Q^2)}{2}.$$
--
--   Counts and queries are interpreted in $\mathbb Q$, so signed intermediates are never truncated.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 26, §5.3.3, inversion and positive count

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 26, determinant, inversion, and the first inverse column. -/
theorem positive_count {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (z : List R) (q : Polynomial R) :
    Matrix.det ctmat1 = 2 ∧
    cvec1 z q = Matrix.vecMul (tvec1 z q) ctmat1⁻¹ ∧
    (constraints1 z q 1 : ℚ) = ((taq z q : ℚ) + (taq z (q ^ 2) : ℚ)) / 2 := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
