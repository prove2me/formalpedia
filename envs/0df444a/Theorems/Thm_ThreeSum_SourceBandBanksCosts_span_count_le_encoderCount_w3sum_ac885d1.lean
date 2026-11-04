-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_span_count_le_encoderCount_w3sum_ac885d1
-- name    : ThreeSum.SourceBandBanksCosts.span_count_le_encoderCount_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:06.551923+00:00
-- url     : https://prove2.me/theorems/3c96784d-a7c5-4ca3-ada2-54cee28305ea
-- title:
--   Source Band Banks Costs: span count le encoder Count
-- statement:
--   The Source Band Banks Costs construction uses the span count le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L103-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L103-L136

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.span_count_le_encoderCount_w3sum_ac885d1 {G n : ℕ} (hG : G ≤ bandCount n) :
    G*SourceBandBankLayout.span (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      storageFactor n*encoderCount n := by sorry
