-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryParallelBudget_radix_time_bound
-- name    : ThreeSum.LightTernaryParallelBudget.radix_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:15.464444+00:00
-- url     : https://prove2.me/theorems/42ef2ea8-6b82-4d52-bb23-cbb0fb76abd0
-- title:
--   Light Ternary Parallel Budget: radix time bound
-- statement:
--   Every prefix stage is charged; no source-array generation is free.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryParallelBudget.lean#L5-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryParallelBudget.lean#L5-L20

import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryParallelBudget

theorem ThreeSum.LightTernaryParallelBudget.radix_time_bound (N : ℕ) (hN : 1≤N) : ∀ J,
    LightRadixKeys.time N J ≤ 500*(J+1)*(N^J+N+1) := by sorry
