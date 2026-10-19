-- Prove2me | Theorems.Thm_PermanentRollout_affine_zeroLocus_finite_of_moduleFinite_quotient
-- name    : PermanentRollout.affine_zeroLocus_finite_of_moduleFinite_quotient
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/fcca9250-9e69-4e39-83b6-b6f13ee42850
-- title:
--   PermanentRollout.affine_zeroLocus_finite_of_moduleFinite_quotient
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.affine_zeroLocus_finite_of_moduleFinite_quotient
    {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    (hfinite : Module.Finite ℂ (MvPolynomial ι ℂ ⧸ I)) :
    (MvPolynomial.zeroLocus ℂ I).Finite := by sorry
