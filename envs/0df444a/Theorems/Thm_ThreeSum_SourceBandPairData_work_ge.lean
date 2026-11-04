-- Prove2me | Theorems.Thm_ThreeSum_SourceBandPairData_work_ge
-- name    : ThreeSum.SourceBandPairData.work_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:09.62065+00:00
-- url     : https://prove2.me/theorems/8ec96e1c-2407-49b1-ab05-45666aac5242
-- title:
--   Source Band Pair Data: work ge
-- statement:
--   The Source Band Pair Data construction uses the work ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L14-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandPairData.lean#L14-L16

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairData
open Light BandPartition

theorem ThreeSum.SourceBandPairData.work_ge (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by sorry
