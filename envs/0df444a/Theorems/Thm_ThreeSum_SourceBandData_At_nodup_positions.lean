-- Prove2me | Theorems.Thm_ThreeSum_SourceBandData_At_nodup_positions
-- name    : ThreeSum.SourceBandData.At.nodup_positions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:59.751461+00:00
-- url     : https://prove2.me/theorems/94c9d394-7527-4a04-9b65-9bd44e9628a2
-- title:
--   At: nodup positions
-- statement:
--   The At construction uses the nodup positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L108-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandData.lean#L108-L114

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout

theorem ThreeSum.SourceBandData.At.nodup_positions {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i r : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m) (hr : r < m) :
    (positions μ base n g m i r).Nodup := by sorry
