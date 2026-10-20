-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingBlock_floor_bound
-- name    : PermanentFormulaLowerBound.matchingBlock_floor_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/c15b5aef-b168-4faa-9783-7ee3643f207b
-- title:
--   PermanentFormulaLowerBound.matchingBlock_floor_bound
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

theorem PermanentFormulaLowerBound.matchingBlock_floor_bound (n k : ℕ)
    (hk : 0 < k) (hkn : k ≤ n) :
    n ≤ 2 * (k * (n / k)) := by sorry
