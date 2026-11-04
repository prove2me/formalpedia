-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverLayout_schedule_end_le_space
-- name    : ThreeSum.LightLocalCoverLayout.schedule_end_le_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:38.108486+00:00
-- url     : https://prove2.me/theorems/8f5a96f8-4329-441b-8002-14ba19508222
-- title:
--   Light Local Cover Layout: schedule end le space
-- statement:
--   The Light Local Cover Layout construction uses the schedule end le space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverLayout.lean#L38-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverLayout.lean#L38-L39

import Definitions.Def_Submission_ThreeSum_LightLocalCoverBuild
import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverLayout
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

theorem ThreeSum.LightLocalCoverLayout.schedule_end_le_space (base h : ℕ) :
    scheduleMaps base h+scheduleSize h*(2*(512*h)) ≤ space base h := by sorry
