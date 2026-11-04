-- Prove2me | Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_emod
-- name    : ThreeSum.LightReportingCatalogLookup.word_emod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:07:26.8956+00:00
-- url     : https://prove2.me/theorems/1def9c01-1d16-4187-b757-0c577c7ac7e4
-- title:
--   Light Reporting Catalog Lookup: word emod
-- statement:
--   The Light Reporting Catalog Lookup construction uses the word emod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean#L35-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean#L35-L35

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

theorem ThreeSum.LightReportingCatalogLookup.word_emod (W n : ℕ) : 4*valueBound W n+4*(n+1)+16 ≤ word W n := by sorry
