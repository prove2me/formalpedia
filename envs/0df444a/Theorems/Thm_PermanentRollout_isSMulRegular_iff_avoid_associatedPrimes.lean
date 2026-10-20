-- Prove2me | Theorems.Thm_PermanentRollout_isSMulRegular_iff_avoid_associatedPrimes
-- name    : PermanentRollout.isSMulRegular_iff_avoid_associatedPrimes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/0354ccca-51c8-46db-8eaf-4fe2d1488530
-- title:
--   PermanentRollout.isSMulRegular_iff_avoid_associatedPrimes
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

theorem PermanentRollout.isSMulRegular_iff_avoid_associatedPrimes
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔
      ∀ P ∈ associatedPrimes R M, r ∉ P := by sorry
