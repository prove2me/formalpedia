-- Prove2me | Theorems.Thm_ThreeSum_SourceBandHostCosts_occurrenceRows_le_encoderCount
-- name    : ThreeSum.SourceBandHostCosts.occurrenceRows_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:33:47.536227+00:00
-- url     : https://prove2.me/theorems/bcd69f5a-9374-49b9-a6e6-f301f670f98a
-- title:
--   Source Band Host Costs: occurrence Rows le encoder Count
-- statement:
--   The Source Band Host Costs construction uses the occurrence Rows le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L26-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L26-L31

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceBandHostCosts.occurrenceRows_le_encoderCount {n : ℕ} (hn : 0 < n) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*blockCount (inputBits n) ≤
      blockCount (inputBits n)*encoderCount n := by sorry
