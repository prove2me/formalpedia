-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousComponent_mul_of_right_isHomogeneous_of_lt
-- name    : PermanentRollout.homogeneousComponent_mul_of_right_isHomogeneous_of_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/8080750f-2d7f-4aca-a5a6-b243a26146e0
-- title:
--   PermanentRollout.homogeneousComponent_mul_of_right_isHomogeneous_of_lt
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

theorem PermanentRollout.homogeneousComponent_mul_of_right_isHomogeneous_of_lt
    {ι : Type*} (g f : MvPolynomial ι ℂ) {e n : ℕ}
    (hf : f.IsHomogeneous e) (hn : n < e) :
    MvPolynomial.homogeneousComponent n (g * f) = 0 := by sorry
