-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_space_le_encoderCount
-- name    : ThreeSum.SourceBandBanksCosts.space_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:18.484454+00:00
-- url     : https://prove2.me/theorems/2369ed86-f252-428e-8c12-fbeaf44e9c23
-- title:
--   Source Band Banks Costs: space le encoder Count
-- statement:
--   The Source Band Banks Costs construction uses the space le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L144-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L144-L152

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.space_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandBanks.space base NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+storageFactor n*encoderCount n+Nat.log 2 (scheduleCount n+1)+7 := by sorry
