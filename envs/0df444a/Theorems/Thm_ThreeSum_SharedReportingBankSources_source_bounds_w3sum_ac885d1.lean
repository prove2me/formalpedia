-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_source_bounds_w3sum_ac885d1
-- name    : ThreeSum.SharedReportingBankSources.source_bounds_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:19:35.024517+00:00
-- url     : https://prove2.me/theorems/1f12f52b-00fc-401a-bf30-736ca264ab8a
-- title:
--   Shared Reporting Bank Sources: source bounds
-- statement:
--   The Shared Reporting Bank Sources construction uses the source bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSourceBounds.lean#L10-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSourceBounds.lean#L10-L38

import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light SubsetAddress BlockIndexedQuery GlobalEncoding

theorem ThreeSum.SharedReportingBankSources.source_bounds_w3sum_ac885d1 {base NB NC g h J cut i s : ℕ}
    (hi : i < SourceBandPairSlices.count NB NC g)
    (hs : s < LightBlockSourceCatalog.count h J) :
    leftCell base h J cut i s < SourceBandBankData.finish base NB NC g h J cut ∧
    rightCell base h J cut i s < SourceBandBankData.finish base NB NC g h J cut ∧
    leftBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut ∧
    rightBase base h J cut i s+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤
      SourceBandBankData.finish base NB NC g h J cut := by sorry
