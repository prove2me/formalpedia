-- Prove2me | Theorems.Thm_ThreeSum_SourceBandHostCosts_space_le_encoderCount_w3sum_ac885d1
-- name    : ThreeSum.SourceBandHostCosts.space_le_encoderCount_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:16:00.891942+00:00
-- url     : https://prove2.me/theorems/4d36939f-8f75-4ac2-84d7-eb56f59e2bc8
-- title:
--   Source Band Host Costs: space le encoder Count
-- statement:
--   The Source Band Host Costs construction uses the space le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L53-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandHostCosts.lean#L53-L69

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_space_le_encoderCount

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceBandHostCosts.space_le_encoderCount_w3sum_ac885d1 {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+
        Nat.log 2 (scheduleCount n+1)+
        max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+16 := by sorry
