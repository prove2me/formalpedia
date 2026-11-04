-- Prove2me | Theorems.Thm_ThreeSum_SourceControlCosts_finish_le_encoderCount
-- name    : ThreeSum.SourceControlCosts.finish_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:35:56.343116+00:00
-- url     : https://prove2.me/theorems/0c334a81-745c-4ac3-bc41-cb00f7146810
-- title:
--   Source Control Costs: finish le encoder Count
-- statement:
--   The Source Control Costs construction uses the finish le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean#L51-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean#L51-L57

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_finish_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandHostCosts_finish_le_encoderCount

set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceControlCosts.finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+17 := by sorry
