-- Prove2me | Theorems.Thm_PermanentRollout_affine_output_equation_totalDegree_le_one
-- name    : PermanentRollout.affine_output_equation_totalDegree_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/9becf6dc-0c20-4ce6-90dc-0de5cd259a24
-- title:
--   PermanentRollout.affine_output_equation_totalDegree_le_one
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.affine_output_equation_totalDegree_le_one
    {ι : Type*} (output : MvPolynomial ι ℂ) (η : ℂ)
    (houtput : output.totalDegree ≤ 1) :
    (output - MvPolynomial.C η).totalDegree ≤ 1 := by sorry
