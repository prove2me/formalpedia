-- Prove2me | Theorems.Thm_ThreeSum_SourceBandBankData_Stored_of_kept_w3sum_ac885d1
-- name    : ThreeSum.SourceBandBankData.Stored.of_kept_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:36:40.735393+00:00
-- url     : https://prove2.me/theorems/f7b62ef7-da3b-48e5-b18e-3d8ef4655163
-- title:
--   Stored: of kept
-- statement:
--   The Stored construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankData.lean#L34-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankData.lean#L34-L50

import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Definitions.Def_Submission_ThreeSum_SourceBandBankData
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankData
open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords

theorem ThreeSum.SourceBandBankData.Stored.of_kept_w3sum_ac885d1 {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g h J cut occ bound : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift)
    (K : Kept μ ν bound) (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hb : finish base NL NR g h J cut ≤ bound) :
    Stored ν fL fR base NL NR g h J cut occ p shift := by sorry
