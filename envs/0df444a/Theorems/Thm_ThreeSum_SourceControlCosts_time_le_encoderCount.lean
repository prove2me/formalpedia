-- Prove2me | Theorems.Thm_ThreeSum_SourceControlCosts_time_le_encoderCount
-- name    : ThreeSum.SourceControlCosts.time_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:34:19.049226+00:00
-- url     : https://prove2.me/theorems/eb8f721d-e614-4f56-9803-dc716ca7429b
-- title:
--   Source Control Costs: time le encoder Count
-- statement:
--   The Source Control Costs construction uses the time le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean#L37-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean#L37-L49

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_WeightedCache3SUM_Alias_1a074e2b77e127b6
import Definitions.Def_WeightedCache3SUM_Alias_8b3592271bea283a
import Theorems.Thm_ThreeSum_SourceBandHostCosts_time_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandPairCosts_time_le_encoderCount

set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceControlCosts.time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
        factor (microHalf (inputBits n)) (blockCount (inputBits n))+5705)*encoderCount n+4859 := by sorry
