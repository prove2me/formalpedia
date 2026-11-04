-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairCosts_tableCount_le_encoderCount
-- name    : ThreeSum.SourceBandPairCosts.tableCount_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:16:34.763649+00:00
-- url     : https://prove2.me/theorems/7bf08d5b-1c42-4326-b22d-f7e4201fe77b
-- title:
--   Source Band Pair Costs: table Count le encoder Count
-- statement:
--   The Source Band Pair Costs construction uses the table Count le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean#L28-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairCosts.lean#L28-L38

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData

theorem ThreeSum.SourceBandPairCosts.tableCount_le_encoderCount {n : ℕ} (hn : 0 < n) : tableCount n ≤ encoderCount n := by sorry
