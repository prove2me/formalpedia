-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_homogeneous_isSMulRegular_of_linear_hyperplane_aux
-- name    : PermanentRollout.homogeneousMap_allRank_homogeneous_isSMulRegular_of_linear_hyperplane_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/10881e1a-f0f6-445e-b175-0f0d375ffc49
-- title:
--   PermanentRollout.homogeneousMap_allRank_homogeneous_isSMulRegular_of_linear_hyperplane_aux
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousMap_allRank_homogeneous_isSMulRegular_of_linear_hyperplane_aux
    {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (f ell : MvPolynomial ι ℂ) {e : ℕ}
    (hf : f.IsHomogeneous e)
    (hellhom : ell.IsHomogeneous 1)
    (hellregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) ell)
    (hfmod : IsSMulRegular
      (MvPolynomial ι ℂ ⧸
        (I ⊔ Ideal.span ({ell} : Set (MvPolynomial ι ℂ)))) f) :
    IsSMulRegular (MvPolynomial ι ℂ ⧸ I) f := by sorry
