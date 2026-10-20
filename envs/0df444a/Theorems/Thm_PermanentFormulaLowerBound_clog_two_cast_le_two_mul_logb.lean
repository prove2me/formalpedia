-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_clog_two_cast_le_two_mul_logb
-- name    : PermanentFormulaLowerBound.clog_two_cast_le_two_mul_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/1c040793-264d-46a1-b296-7fcae4d797c7
-- title:
--   PermanentFormulaLowerBound.clog_two_cast_le_two_mul_logb
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

theorem PermanentFormulaLowerBound.clog_two_cast_le_two_mul_logb {n : ℕ} (hn : 2 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 (n : ℝ) := by sorry
