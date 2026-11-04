-- Prove2me | Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_search
-- name    : ThreeSum.LightReportingCatalogLookup.word_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:08:17.545675+00:00
-- url     : https://prove2.me/theorems/532937b3-d948-4f91-bd8a-fa4431160a9b
-- title:
--   Light Reporting Catalog Lookup: word search
-- statement:
--   The Light Reporting Catalog Lookup construction uses the word search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean#L34-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean#L34-L34

import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingCatalogLookup
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 8000
variable {lim : Limits}

theorem ThreeSum.LightReportingCatalogLookup.word_search (W n : ℕ) : n+2^((2*W+1)+1)+16 ≤ word W n := by sorry
