-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPrefixCatalog_count_eq_length
-- name    : ThreeSum.LightReportingPrefixCatalog.count_eq_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:01:49.625029+00:00
-- url     : https://prove2.me/theorems/18650f66-e564-42e5-a852-fa8935507a29
-- title:
--   Light Reporting Prefix Catalog: count eq length
-- statement:
--   The Light Reporting Prefix Catalog construction uses the count eq length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L48-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L48-L49

import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPrefixCatalog
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}

theorem ThreeSum.LightReportingPrefixCatalog.count_eq_length (h k : ℕ) : count h k = (prefixes h k).length := by sorry
