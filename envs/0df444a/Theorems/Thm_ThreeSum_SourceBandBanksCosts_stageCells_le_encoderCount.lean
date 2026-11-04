-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_stageCells_le_encoderCount
-- name    : ThreeSum.SourceBandBanksCosts.stageCells_le_encoderCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:05.066864+00:00
-- url     : https://prove2.me/theorems/eea56dcc-4145-45c7-b291-1d87bb47fb5a
-- title:
--   Source Band Banks Costs: stage Cells le encoder Count
-- statement:
--   The Source Band Banks Costs construction uses the stage Cells le encoder Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L34-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L34-L45

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.stageCells_le_encoderCount {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    stageCells NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      (256*mu n+1)*(mu n+1)*encoderCount n := by sorry
