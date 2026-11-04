-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_stageCells_eq
-- name    : ThreeSum.SourceBandBanksCosts.stageCells_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:59.546168+00:00
-- url     : https://prove2.me/theorems/9154e233-1ca3-4504-b709-3605dafca1d9
-- title:
--   Source Band Banks Costs: stage Cells eq
-- statement:
--   The Source Band Banks Costs construction uses the stage Cells eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L16-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L16-L21

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.stageCells_eq (NL NR g h J cut : ℕ) :
    stageCells NL NR g h J cut=
      2*SourceBandPairSlices.count NL NR g*LightBlockSourceCatalog.count h J*
        (J*(512*h)+1)*downsetCap (J*(512*h)) cut := by sorry
