-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankLayout_word_mono
-- name    : ThreeSum.SourceBandBankLayout.word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:59:04.759198+00:00
-- url     : https://prove2.me/theorems/cf387499-422c-44db-9038-46552a141ce4
-- title:
--   Source Band Bank Layout: word mono
-- statement:
--   The Source Band Bank Layout construction uses the word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L46-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L46-L51

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder

theorem ThreeSum.SourceBandBankLayout.word_mono {NL NR NL' NR' h J : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    LightBlockSourceRetainedHost.word NL NR h J ≤ LightBlockSourceRetainedHost.word NL' NR' h J := by sorry
