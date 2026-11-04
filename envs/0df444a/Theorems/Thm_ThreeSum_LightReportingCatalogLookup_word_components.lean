-- Prove2me | Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_components
-- name    : ThreeSum.LightReportingCatalogLookup.word_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:08:26.779887+00:00
-- url     : https://prove2.me/theorems/a8eb99ce-2de0-4ac2-a426-f4c242aa381a
-- title:
--   Light Reporting Catalog Lookup: word components
-- statement:
--   The Light Reporting Catalog Lookup construction uses the word components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean#L28-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean#L28-L30

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

theorem ThreeSum.LightReportingCatalogLookup.word_components (U n A B : ℕ) :
    U ≤ 4*U+4*(n+1)+n+A+B+16 ∧ A ≤ 4*U+4*(n+1)+n+A+B+16 ∧
    n+A+16 ≤ 4*U+4*(n+1)+n+A+B+16 ∧ 4*U+4*(n+1)+16 ≤ 4*U+4*(n+1)+n+A+B+16 := by sorry
