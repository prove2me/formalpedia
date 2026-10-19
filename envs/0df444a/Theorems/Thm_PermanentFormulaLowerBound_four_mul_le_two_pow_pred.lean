-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_four_mul_le_two_pow_pred
-- name    : PermanentFormulaLowerBound.four_mul_le_two_pow_pred
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/efe76802-7579-48fc-b945-2a9dc228bf41
-- title:
--   PermanentFormulaLowerBound.four_mul_le_two_pow_pred
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

theorem PermanentFormulaLowerBound.four_mul_le_two_pow_pred (ell : ℕ) (hell : 6 ≤ ell) :
    4 * ell ≤ 2 ^ (ell - 1) := by sorry
