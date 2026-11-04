-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_source_card_le
-- name    : ThreeSum.SharedReportingBankSources.source_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:19:04.933825+00:00
-- url     : https://prove2.me/theorems/5d3cf9c0-f0e6-41ea-bb58-36b25529c55a
-- title:
--   Shared Reporting Bank Sources: source card le
-- statement:
--   The Shared Reporting Bank Sources construction uses the source card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSourceBounds.lean#L40-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSourceBounds.lean#L40-L42

import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light SubsetAddress BlockIndexedQuery GlobalEncoding

theorem ThreeSum.SharedReportingBankSources.source_card_le (n g i : ℕ) : (SourceBandPartition.source n g i).card ≤ g := by sorry
