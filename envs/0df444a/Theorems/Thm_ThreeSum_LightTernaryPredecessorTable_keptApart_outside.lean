-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_keptApart_outside
-- name    : ThreeSum.LightTernaryPredecessorTable.keptApart_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:00.033315+00:00
-- url     : https://prove2.me/theorems/cfbb28e7-cb84-4f7c-8080-fd470533b713
-- title:
--   Light Ternary Predecessor Table: kept Apart outside
-- statement:
--   The Light Ternary Predecessor Table construction uses the kept Apart outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean#L47-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessorTable.lean#L47-L54

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryPredecessorTable.keptApart_outside {μ ν : ℕ → ℤ} {dst stride n : ℕ}
    (hs : 0<stride) (H : KeptApart μ ν dst stride n) : SameOutside μ ν dst (2*stride*n) := by sorry
