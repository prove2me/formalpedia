-- Prove2me | Theorems.Thm_ThreeSum_BlockSourceStageCosts_work_le_encoderCount
-- name    : ThreeSum.BlockSourceStageCosts.work_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:45:24.256898+00:00
-- url     : https://prove2.me/theorems/0efb59d6-c4a2-4160-b099-83a20c44df73
-- title:
--   Block Source Stage Costs: work le encoder Count
-- statement:
--   The Block Source Stage Costs construction uses the work le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceStageCosts.lean#L21-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BlockSourceStageCosts.lean#L21-L43

import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceStageCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing

theorem ThreeSum.BlockSourceStageCosts.work_le_encoderCount (n : ℕ) :
    work n ≤ LightBlockSourceRetainedProgram.factor
      (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)*encoderCount n := by sorry
