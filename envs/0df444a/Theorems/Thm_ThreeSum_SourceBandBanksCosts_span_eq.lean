-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBanksCosts_span_eq
-- name    : ThreeSum.SourceBandBanksCosts.span_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:24:15.121454+00:00
-- url     : https://prove2.me/theorems/7fc193b3-0504-48f7-bc79-b4421149e4ac
-- title:
--   Source Band Banks Costs: span eq
-- statement:
--   The Source Band Banks Costs construction uses the span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L85-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBanksCosts.lean#L85-L93

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

theorem ThreeSum.SourceBandBanksCosts.span_eq (h J cut : ℕ) : SourceBandBankLayout.span h J cut=
    LightBlockSourceCatalog.count h J*(LightBlockSourceBatchLayout.stride (J*(512*h)) cut+2)+
      downsetCap (J*(512*h)) cut+J*(512*h)+2+LightBlockSourceRetainedHost.space 0 h J := by sorry
