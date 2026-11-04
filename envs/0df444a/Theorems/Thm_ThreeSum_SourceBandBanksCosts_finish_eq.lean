-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_finish_eq
-- name    : ThreeSum.SourceBandBanksCosts.finish_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:23.213044+00:00
-- url     : https://prove2.me/theorems/ccaf56c1-737d-4ceb-b981-8252438b9011
-- title:
--   Source Band Banks Costs: finish eq
-- statement:
--   The Source Band Banks Costs construction uses the finish eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L95-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L95-L97

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.finish_eq (base NL NR g h J cut : ℕ) :
    SourceBandBankData.finish base NL NR g h J cut=
      base+5+SourceBandPairSlices.count NL NR g*SourceBandBankLayout.span h J cut := by sorry
