-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_time_le_encoderCount_w3sum_ac885d1
-- name    : ThreeSum.SourceBandBanksCosts.time_le_encoderCount_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:02:44.498013+00:00
-- url     : https://prove2.me/theorems/35d22a83-3325-4baa-a150-41350d10a917
-- title:
--   Source Band Banks Costs: time le encoder Count
-- statement:
--   The Source Band Banks Costs construction uses the time le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L54-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L54-L75

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_WeightedCache3SUM_Alias_8b3592271bea283a
import Theorems.Thm_ThreeSum_SourceBandPairCosts_time_le_encoderCount

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.time_le_encoderCount_w3sum_ac885d1 {NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandBanks.time NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+1300)*
        encoderCount n+1220 := by sorry
