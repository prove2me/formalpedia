-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_finish_le_encoderCount
-- name    : ThreeSum.SourceBandBanksCosts.finish_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:23:22.732031+00:00
-- url     : https://prove2.me/theorems/9e9bf76c-2f4b-419b-a913-6c72743584b0
-- title:
--   Source Band Banks Costs: finish le encoder Count
-- statement:
--   The Source Band Banks Costs construction uses the finish le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L138-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L138-L142

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.finish_le_encoderCount {base NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandBankData.finish base NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+5+storageFactor n*encoderCount n := by sorry
