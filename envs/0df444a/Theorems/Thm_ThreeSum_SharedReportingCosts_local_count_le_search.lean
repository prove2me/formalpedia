-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingCosts_local_count_le_search
-- name    : ThreeSum.SharedReportingCosts.local_count_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:19:57.121485+00:00
-- url     : https://prove2.me/theorems/dc8fbecf-6895-4901-ad24-23e410e3d811
-- title:
--   Shared Reporting Costs: local count le search
-- statement:
--   The complete local row-pair enumeration is a subpolynomial microblock
--   factor, including at level zero where the prefix count itself is one.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingCosts.lean#L38-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingCosts.lean#L38-L47

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogCosts
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingCosts
open Scales CostLedger ReportingHostPrefixCatalog
set_option maxHeartbeats 1700000
set_option maxRecDepth 10000

theorem ThreeSum.SharedReportingCosts.local_count_le_search (n : ℕ) : localCount n ≤ localSearch 257 n := by sorry
