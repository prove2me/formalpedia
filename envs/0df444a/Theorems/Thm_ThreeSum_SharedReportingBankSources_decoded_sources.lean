-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankSources_decoded_sources
-- name    : ThreeSum.SharedReportingBankSources.decoded_sources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:11:50.104039+00:00
-- url     : https://prove2.me/theorems/1f078f0f-e8ad-427d-b57a-d1a4e4fae8ad
-- title:
--   Shared Reporting Bank Sources: decoded sources
-- statement:
--   The Shared Reporting Bank Sources construction uses the decoded sources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L41-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankSources.lean#L41-L52

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light GlobalEncoding BlockEncoding BlockIndexedQuery SharedReportingBankData
open BlockSourceOccurrenceOrder BlockSourceSharing OutputDecodeRecords

theorem ThreeSum.SharedReportingBankSources.decoded_sources {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {base NB NC g h J occ i j k : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC base NB NC g h J (2*h*J) occ p shift)
    (hi : i < SourceBandPairSlices.count NB NC g) (hj : j < SourceBandPairSlices.count NB NC g)
    (hk : k < localCount h^J) :
    ReportingHostLevelData.Sources μ p shift
      (SourceBandPartition.source NB g i) (SourceBandPartition.source NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J))
      (leftBase base h J (2*h*J) i (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k))
      (rightBase base h J (2*h*J) j (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)) := by sorry
