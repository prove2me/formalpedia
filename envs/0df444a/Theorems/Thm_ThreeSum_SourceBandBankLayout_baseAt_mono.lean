-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankLayout_baseAt_mono
-- name    : ThreeSum.SourceBandBankLayout.baseAt_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:03:40.448021+00:00
-- url     : https://prove2.me/theorems/1892f2d4-5c6f-4856-b24e-681e9546bc8d
-- title:
--   Source Band Bank Layout: base At mono
-- statement:
--   The Source Band Bank Layout construction uses the base At mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L36-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L36-L38

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder

theorem ThreeSum.SourceBandBankLayout.baseAt_mono (base h J cut : ℕ) : Monotone (baseAt base h J cut) := by sorry
