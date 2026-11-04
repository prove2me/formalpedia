-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankLayout_work_le_end
-- name    : ThreeSum.SourceBandBankLayout.work_le_end
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:00:50.474129+00:00
-- url     : https://prove2.me/theorems/746a6c40-6ee9-47a8-b7c5-4097de4ec00f
-- title:
--   Source Band Bank Layout: work le end
-- statement:
--   The Source Band Bank Layout construction uses the work le end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L40-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L40-L44

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder

theorem ThreeSum.SourceBandBankLayout.work_le_end (base h J cut i : ℕ) :
    work (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤
      baseAt base h J cut (i+1) := by sorry
