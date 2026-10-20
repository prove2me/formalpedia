-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_two_le_leaves_of_fourth_power_bound
-- name    : PermanentFormulaLowerBound.two_le_leaves_of_fourth_power_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/d69e68ab-e419-4207-b433-132d251ae1a0
-- title:
--   PermanentFormulaLowerBound.two_le_leaves_of_fourth_power_bound
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

theorem PermanentFormulaLowerBound.two_le_leaves_of_fourth_power_bound
    {n leaves c : ℕ} (hn : 32 ≤ n) (hc : c ≤ 48)
    (hbound : n ^ 4 ≤ c * (2 * Nat.clog 2 n) * leaves) :
    2 ≤ leaves := by sorry
