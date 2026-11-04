-- Prove2me | Theorems.Thm_ThreeSum_SourceControlCosts_space_le_encoderCount_w3sum_ac885d1
-- name    : ThreeSum.SourceControlCosts.space_le_encoderCount_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:53:11.352845+00:00
-- url     : https://prove2.me/theorems/c0b366cc-de79-4a79-b79a-66011ee8f51a
-- title:
--   Source Control Costs: space le encoder Count
-- statement:
--   The Source Control Costs construction uses the space le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean#L59-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceControlCosts.lean#L59-L76

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_space_le_encoderCount
import Definitions.Def_WeightedCache3SUM_Alias_efe4583c1ba8c927

set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlCosts
open Scales TrimScales StageBounds CostLedger BandScales

theorem ThreeSum.SourceControlCosts.space_le_encoderCount_w3sum_ac885d1 {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n+
          (256*mu n+1)^2+(256*mu n+1))*encoderCount n+
        Nat.log 2 (scheduleCount n+1)+
        max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+19 := by sorry
