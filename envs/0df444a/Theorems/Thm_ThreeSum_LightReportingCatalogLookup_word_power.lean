-- Prove2me | Theorems.Thm_ThreeSum_LightReportingCatalogLookup_word_power
-- name    : ThreeSum.LightReportingCatalogLookup.word_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:08:28.252227+00:00
-- url     : https://prove2.me/theorems/bce387a5-931e-485a-ac18-a3aebdfd39ed
-- title:
--   Light Reporting Catalog Lookup: word power
-- statement:
--   The Light Reporting Catalog Lookup construction uses the word power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean#L33-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogLookup.lean#L33-L33

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

theorem ThreeSum.LightReportingCatalogLookup.word_power (W n : ℕ) : 2^(2*W+2) ≤ word W n := by sorry
