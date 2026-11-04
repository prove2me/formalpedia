-- Prove2me | Theorems.Thm_ThreeSum_SourceBandHostCosts_bankHeader_le_encoderCount
-- name    : ThreeSum.SourceBandHostCosts.bankHeader_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:34:21.625578+00:00
-- url     : https://prove2.me/theorems/d855ef93-e461-41ee-9e08-51ae9ddf4239
-- title:
--   Source Band Host Costs: bank Header le encoder Count
-- statement:
--   The Source Band Host Costs construction uses the bank Header le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L33-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L33-L40

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceBandHostCosts.bankHeader_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) ≤
      base+(29+blockCount (inputBits n))*encoderCount n+9 := by sorry
