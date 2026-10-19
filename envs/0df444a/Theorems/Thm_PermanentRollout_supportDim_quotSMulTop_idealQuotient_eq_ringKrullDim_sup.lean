-- Prove2me | Theorems.Thm_PermanentRollout_supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup
-- name    : PermanentRollout.supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/d5424f4b-9003-4820-be7f-c53348374070
-- title:
--   PermanentRollout.supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.supportDim_quotSMulTop_idealQuotient_eq_ringKrullDim_sup
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    Module.supportDim R (QuotSMulTop x (R ⧸ I)) =
      ringKrullDim (R ⧸ (I ⊔ Ideal.span ({x} : Set R))) := by sorry
