-- Prove2me | Theorems.Thm_ThreeSum_SourceBandHostCosts_finish_le_encoderCount
-- name    : ThreeSum.SourceBandHostCosts.finish_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:06:24.673916+00:00
-- url     : https://prove2.me/theorems/e6de3801-7ea3-42fb-8458-c2abb37c7f00
-- title:
--   Source Band Host Costs: finish le encoder Count
-- statement:
--   The Source Band Host Costs construction uses the finish le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L42-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L42-L51

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_finish_le_encoderCount

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceBandHostCosts.finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+14 := by sorry
