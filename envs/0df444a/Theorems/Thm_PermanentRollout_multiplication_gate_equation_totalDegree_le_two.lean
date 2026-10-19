-- Prove2me | Theorems.Thm_PermanentRollout_multiplication_gate_equation_totalDegree_le_two
-- name    : PermanentRollout.multiplication_gate_equation_totalDegree_le_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/77a8c5d9-8bfd-451d-9d22-a6e55ce05a8b
-- title:
--   PermanentRollout.multiplication_gate_equation_totalDegree_le_two
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout

theorem PermanentRollout.multiplication_gate_equation_totalDegree_le_two
    {ι : Type*} (j : ι) (left right : MvPolynomial ι ℂ)
    (hleft : left.totalDegree ≤ 1)
    (hright : right.totalDegree ≤ 1) :
    (MvPolynomial.X j - left * right).totalDegree ≤ 2 := by sorry
