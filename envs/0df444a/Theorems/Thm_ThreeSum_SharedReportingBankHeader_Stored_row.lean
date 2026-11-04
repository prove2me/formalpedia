-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankHeader_Stored_row
-- name    : ThreeSum.SharedReportingBankHeader.Stored.row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:36:34.694005+00:00
-- url     : https://prove2.me/theorems/4f4ef5c2-17fa-4582-a9fa-d2680c639f17
-- title:
--   Stored: row
-- statement:
--   The Stored construction uses the row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean#L91-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean#L91-L103

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000

theorem ThreeSum.SharedReportingBankHeader.Stored.row {μ : ℕ → ℤ} {free h J NB NC g s i j : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Stored μ free h J NB NC g fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    Built μ (rowRecord (records free) (levels J) (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      (rowBase (payload free h J NB NC g) h J (levels J) (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      h J (levels J)
      (BlockIndexedQuery.leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
        (BlockSourceOccurrenceOrder.representative h J s))
      (BlockIndexedQuery.rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
        (BlockSourceOccurrenceOrder.representative h J s)) := by sorry
