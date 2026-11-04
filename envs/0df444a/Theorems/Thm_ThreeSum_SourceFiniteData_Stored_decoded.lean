-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteData_Stored_decoded
-- name    : ThreeSum.SourceFiniteData.Stored.decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:55:43.890013+00:00
-- url     : https://prove2.me/theorems/3568c5b8-35b8-4210-88d1-f80ec1b87b03
-- title:
--   Stored: decoded
-- statement:
--   The Stored construction uses the decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean#L33-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteData.lean#L33-L44

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_decoded
import Theorems.Thm_ThreeSum_SourceBandFinite_decoded

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA

theorem ThreeSum.SourceFiniteData.Stored.decoded {μ : ℕ → ℤ} {base g p h J cut i k : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (hi : i < SourceBandPairSlices.count B.length C.length g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ
      (SourceBandBankLayout.baseAt
        (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J+5)
        h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k) (p : ℤ) shift
      (finiteBandPositions B.length g i) (fun t : Fin B.length => B.getD t.val 0)
      (finiteBandPositions C.length g i) (fun t : Fin C.length => C.getD t.val 0)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) := by sorry
