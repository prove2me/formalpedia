-- Prove2me | Theorems.Thm_ThreeSum_SourceBandFinite_decoded
-- name    : ThreeSum.SourceBandFinite.decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:37:49.1592+00:00
-- url     : https://prove2.me/theorems/f7a35038-4ac2-4837-9079-9d60cda05b4b
-- title:
--   Source Band Finite: decoded
-- statement:
--   The Source Band Finite construction uses the decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandFinite.lean#L27-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandFinite.lean#L27-L36

import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankData_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_decoded

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandFinite
open GlobalEncoding OutputDecodeRecords

theorem ThreeSum.SourceBandFinite.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ (SourceBandBankLayout.baseAt (base+5) h J cut i)
      (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k) p shift
      (BandRawA.finiteBandPositions NL g i) (fun t : Fin NL => fL t.val)
      (BandRawA.finiteBandPositions NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) := by sorry
