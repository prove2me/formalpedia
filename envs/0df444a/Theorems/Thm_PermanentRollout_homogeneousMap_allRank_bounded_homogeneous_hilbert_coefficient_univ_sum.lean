-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum
-- name    : PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/2d30de8e-56a4-4d7d-9b93-508d6273fa4b
-- title:
--   PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum
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
open scoped Pointwise
open scoped BigOperators

theorem PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum
    (k e : ℕ) (hk : 0 < k) :
    (∑ n ∈ Finset.range (k * e),
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n Finset.univ) =
      e ^ k := by sorry
