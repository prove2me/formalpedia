-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverRetention_table_ends_le
-- name    : ThreeSum.LightLocalCoverRetention.table_ends_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:03.391564+00:00
-- url     : https://prove2.me/theorems/b5ac6346-c73a-42d6-be27-ad73f4d50ce8
-- title:
--   Light Local Cover Retention: table ends le
-- statement:
--   The Light Local Cover Retention construction uses the table ends le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRetention.lean#L17-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRetention.lean#L17-L25

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000

theorem ThreeSum.LightLocalCoverRetention.table_ends_le (base h : ℕ) :
    maps base h+rows h*(2*(512*h)) ≤ nextFree base h ∧
    hist0 base h+rows h*localPrime h ≤ nextFree base h ∧
    hist1 base h+rows h*localPrime h ≤ nextFree base h ∧
    matrixPtr base h+rows h*cols h ≤ nextFree base h ∧
    candidates base h+scheduleSize h ≤ nextFree base h := by sorry
