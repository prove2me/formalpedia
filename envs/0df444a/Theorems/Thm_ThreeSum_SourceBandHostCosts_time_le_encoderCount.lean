-- Prove2me | Theorems.Thm_ThreeSum_SourceBandHostCosts_time_le_encoderCount
-- name    : ThreeSum.SourceBandHostCosts.time_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:28:39.288722+00:00
-- url     : https://prove2.me/theorems/be0abaae-f5c1-4015-8993-1dc9f675e3c6
-- title:
--   Source Band Host Costs: time le encoder Count
-- statement:
--   The Source Band Host Costs construction uses the time le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L10-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L10-L18

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Definitions.Def_WeightedCache3SUM_Alias_1a074e2b77e127b6
import Definitions.Def_WeightedCache3SUM_Alias_8b3592271bea283a
import Theorems.Thm_ThreeSum_SourceBandPairCosts_time_le_encoderCount

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceBandHostCosts.time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+5205)*encoderCount n+4859 := by sorry
