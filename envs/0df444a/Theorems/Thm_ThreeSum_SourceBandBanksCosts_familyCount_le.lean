-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_familyCount_le
-- name    : ThreeSum.SourceBandBanksCosts.familyCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:56.43017+00:00
-- url     : https://prove2.me/theorems/28394d50-1a30-4ec1-8a85-15c2c5c1c15e
-- title:
--   Source Band Banks Costs: family Count le
-- statement:
--   The Source Band Banks Costs construction uses the family Count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L27-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L27-L32

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.familyCount_le {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    familyCount NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) ≤
      2*bandCount n*scheduleCount n := by sorry
