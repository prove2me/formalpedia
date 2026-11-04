-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankLayout_At_decoded
-- name    : ThreeSum.SourceBandBankLayout.At.decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:14:19.942791+00:00
-- url     : https://prove2.me/theorems/13487c4f-1116-45a1-bf69-197ac21655db
-- title:
--   At: decoded
-- statement:
--   The At construction uses the decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L86-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L86-L94

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Theorems.Thm_ThreeSum_LightBlockSourceCatalog_Stored_decoded

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder

theorem ThreeSum.SourceBandBankLayout.At.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i k : ℕ}
    {p shift : ℤ} (H : At μ fL fR base NL NR g h J cut p shift i)
    (hk : k < OutputDecodeRecords.localCount h^J) :
    LightBlockSourceBatch.BankAt μ (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (OutputDecodeRecords.layerCount h) J k)
      p shift (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (OutputDecodeRecords.outputDefault h J)) := by sorry
