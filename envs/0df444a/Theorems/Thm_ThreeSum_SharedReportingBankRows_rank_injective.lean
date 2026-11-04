-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankRows_rank_injective
-- name    : ThreeSum.SharedReportingBankRows.rank_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:40:23.060609+00:00
-- url     : https://prove2.me/theorems/314df5f8-fe65-4503-9859-3552c5ec2c5f
-- title:
--   Shared Reporting Bank Rows: rank injective
-- statement:
--   The Shared Reporting Bank Rows construction uses the rank injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L28-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankRows.lean#L28-L33

import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankRows
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1800000

theorem ThreeSum.SharedReportingBankRows.rank_injective {nb nc s i j s' i' j' : ℕ}
    (hi : i < nb) (hj : j < nc) (hi' : i' < nb) (hj' : j' < nc)
    (he : rank nb nc s i j=rank nb nc s' i' j') : s=s' ∧ i=i' ∧ j=j' := by sorry
