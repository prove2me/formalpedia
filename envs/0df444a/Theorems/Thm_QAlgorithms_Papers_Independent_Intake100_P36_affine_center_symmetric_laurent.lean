-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_affine_center_symmetric_laurent
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.affine_center_symmetric_laurent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:58:09.903839+00:00
-- url     : https://prove2.me/theorems/9a055a38-80ab-4a5e-aa38-f03e685f15c2
-- title:
--   Bernstein’s description of the affine Hecke center
-- statement:
--   Let R be an algebraically closed field, q∈R×, and n≥0. Let Ĥ_n be the extended affine Hecke algebra with generators T₁,…,Tₙ₋₁ and invertible X₁,…,Xₙ, the quadratic relation (T_i−q)(T_i+1)=0, braid relations, commuting X variables, T_iX_iT_i=qX_{i+1}, and T_iX_j=X_jT_i when j≠i,i+1. Then
--
--   $$Z(\widehat H_n)=R[X_1^{\pm1},\ldots,X_n^{\pm1}]^{S_n}.$$
--
--   Laurent polynomials permit all integer exponents. The presentation corrects the printed right-hand side and misplaced shared distance restriction on PDF p.7.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 37, Theorem 5.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 5.4 (Bernstein), PDF p.37: the full center is symmetric LAURENT polynomials.
The degree-zero Laurent algebra has only the empty exponent and is the scalar algebra. -/
theorem affine_center_symmetric_laurent {R : Type*} [Field R] [IsAlgClosed R]
    (q : Rˣ) (n : ℕ) :
    ∀ z : AffineHecke q n,
      z ∈ Subalgebra.center R (AffineHecke q n) ↔
        ∃ p : Laurent R n, IsSymmetricLaurent p ∧ affineLaurentEval q p = z := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
