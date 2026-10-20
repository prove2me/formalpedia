-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMap_allRank_isSMulRegular_sup_of_quotient_map_aux
-- name    : PermanentRollout.homogeneousMap_allRank_isSMulRegular_sup_of_quotient_map_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:36.286012+00:00
-- url     : https://prove2.me/theorems/9ee41cb5-4021-4718-81b0-dd233a387da3
-- title:
--   PermanentRollout.homogeneousMap_allRank_isSMulRegular_sup_of_quotient_map_aux
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

theorem PermanentRollout.homogeneousMap_allRank_isSMulRegular_sup_of_quotient_map_aux
    {R : Type*} [CommRing R]
    (I J : Ideal R) (g : R)
    (hregular : IsSMulRegular
      ((R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J))
      (Ideal.Quotient.mk J g)) :
    IsSMulRegular (R ⧸ (I ⊔ J)) g := by sorry
