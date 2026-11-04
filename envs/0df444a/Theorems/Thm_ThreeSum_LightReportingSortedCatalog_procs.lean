-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSortedCatalog_procs
-- name    : ThreeSum.LightReportingSortedCatalog.procs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:11:25.805066+00:00
-- url     : https://prove2.me/theorems/847e31f7-3d06-4c65-b95e-42e4b3135596
-- title:
--   Light Reporting Sorted Catalog: procs
-- statement:
--   The Light Reporting Sorted Catalog construction uses the procs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSortedCatalog.lean#L31-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSortedCatalog.lean#L31-L31

import Definitions.Def_Submission_ThreeSum_LightReportingPackKeys
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSortedCatalog
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
variable {lim : Limits}

theorem ThreeSum.LightReportingSortedCatalog.procs : MergeSort.Procs program 2 3 4 5 := by sorry
