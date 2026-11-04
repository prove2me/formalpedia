-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_gathered_schedule_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverTables.Data.gathered_schedule_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:25:30.652769+00:00
-- url     : https://prove2.me/theorems/f472e68b-bcf9-4e3c-b630-5253a3c8384e
-- title:
--   Data: gathered schedule
-- statement:
--   The Data construction uses the gathered schedule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L86-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L86-L106

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

theorem ThreeSum.LightLocalCoverTables.Data.gathered_schedule_w3sum_ac885d1 {μ ν : ℕ → ℤ} {h maps hist0 hist1 matrixPtr dst : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr)
    (hcopy : ∀ s < scheduleSize h, ∀ a < 2*(512*h),
      ν (dst+s*(2*(512*h))+a) = μ (maps+(indices h).getD s 0*(2*(512*h))+a)) :
    ScheduleRows ν h dst := by sorry
