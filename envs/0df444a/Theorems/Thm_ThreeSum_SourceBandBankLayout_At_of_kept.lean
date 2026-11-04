-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
-- name    : ThreeSum.SourceBandBankLayout.At.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:00:39.295521+00:00
-- url     : https://prove2.me/theorems/ff407fd5-2590-49a8-bf25-e1789645de63
-- title:
--   At: of kept
-- statement:
--   The At construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L79-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankLayout.lean#L79-L84

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder

theorem ThreeSum.SourceBandBankLayout.At.of_kept {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i bound : ℕ}
    {p shift : ℤ} (H : At μ fL fR base NL NR g h J cut p shift i)
    (K : Kept μ ν bound) (hb : baseAt base h J cut (i+1) ≤ bound) :
    At ν fL fR base NL NR g h J cut p shift i := by sorry
