-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingCosts_levels_time_le
-- name    : ThreeSum.SharedReportingCosts.levels_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:20:19.957298+00:00
-- url     : https://prove2.me/theorems/a1f015b0-28ac-4b39-a88f-8fd6338d39ae
-- title:
--   Shared Reporting Costs: levels time le
-- statement:
--   The Shared Reporting Costs construction uses the levels time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingCosts.lean#L123-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingCosts.lean#L123-L129

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

theorem ThreeSum.SharedReportingCosts.levels_time_le (n : ℕ) : levelsTime n ≤ overhead n*allPrefixBoxes n := by sorry
