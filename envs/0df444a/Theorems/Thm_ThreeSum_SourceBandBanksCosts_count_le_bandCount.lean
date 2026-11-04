-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_count_le_bandCount
-- name    : ThreeSum.SourceBandBanksCosts.count_le_bandCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:21.475717+00:00
-- url     : https://prove2.me/theorems/d03e7063-0bba-46e1-a732-7917fab8c750
-- title:
--   Source Band Banks Costs: count le band Count
-- statement:
--   The Source Band Banks Costs construction uses the count le band Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L23-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L23-L25

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.count_le_bandCount {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandPairSlices.count NL NR (bandSize n) ≤ bandCount n := by sorry
