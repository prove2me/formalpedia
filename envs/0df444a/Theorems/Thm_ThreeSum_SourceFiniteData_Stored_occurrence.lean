-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteData_Stored_occurrence
-- name    : ThreeSum.SourceFiniteData.Stored.occurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:53:45.253794+00:00
-- url     : https://prove2.me/theorems/0ea0dbe4-29d9-4810-a848-5dc259557cd4
-- title:
--   Stored: occurrence
-- statement:
--   The Stored construction uses the occurrence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean#L21-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean#L21-L31

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Theorems.Thm_ThreeSum_SourceBandFinite_occurrence

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA

theorem ThreeSum.SourceFiniteData.Stored.occurrence {μ : ℕ → ℤ} {base g p h J cut i k : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (hi : i < SourceBandPairSlices.count B.length C.length g) (hk : k < LightBlockSourceCatalog.count h J) :
    LightBlockSourceBatch.BankAt μ
      (SourceBandBankLayout.baseAt
        (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J+5)
        h J cut i) (LightBlockSourceCatalog.count h J) cut k (p : ℤ) shift
      (finiteBandPositions B.length g i) (fun t : Fin B.length => B.getD t.val 0)
      (finiteBandPositions C.length g i) (fun t : Fin C.length => C.getD t.val 0)
      (BlockSourceOccurrenceOrder.representative h J k) := by sorry
