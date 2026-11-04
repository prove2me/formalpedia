-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankData_Stored_decoded
-- name    : ThreeSum.SourceBandBankData.Stored.decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:26:15.832854+00:00
-- url     : https://prove2.me/theorems/ce74ff22-ff4b-47a5-9312-fbf54087d5a9
-- title:
--   Stored: decoded
-- statement:
--   The Stored construction uses the decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankData.lean#L24-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankData.lean#L24-L32

import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_decoded

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankData
open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords

theorem ThreeSum.SourceBandBankData.Stored.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ (baseAt (first base) h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)
      p shift (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) := by sorry
