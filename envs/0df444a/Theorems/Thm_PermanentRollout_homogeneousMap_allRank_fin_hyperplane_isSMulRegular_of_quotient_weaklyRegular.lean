-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
-- name    : PermanentRollout.homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/eb1b851b-4610-4e09-801f-ae6a92d43e3b
-- title:
--   PermanentRollout.homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
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
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators

theorem PermanentRollout.homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
    {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (f : Fin n → R) (ell : R) (hell : ell ≠ 0)
    (hregular :
      RingTheory.Sequence.IsWeaklyRegular
        (R ⧸ Ideal.span ({ell} : Set R))
        (List.ofFn fun i : Fin n =>
          Ideal.Quotient.mk (Ideal.span ({ell} : Set R)) (f i))) :
    IsSMulRegular (R ⧸ Ideal.span (Set.range f)) ell := by sorry
