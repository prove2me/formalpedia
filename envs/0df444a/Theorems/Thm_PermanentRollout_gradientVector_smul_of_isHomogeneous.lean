-- Prove2me | Theorems.Thm_PermanentRollout_gradientVector_smul_of_isHomogeneous
-- name    : PermanentRollout.gradientVector_smul_of_isHomogeneous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/d69e99ea-3bca-4a47-8ce2-5a9e5f3aa4ff
-- title:
--   PermanentRollout.gradientVector_smul_of_isHomogeneous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization

theorem PermanentRollout.gradientVector_smul_of_isHomogeneous {m d : ℕ}
    (P : MvPolynomial (Fin m) ℂ) (hP : P.IsHomogeneous d)
    (a : ℂ) (v : Fin m → ℂ) :
    gradientVector P (a • v) = a ^ (d - 1) • gradientVector P v := by sorry
