-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankHeader_Stored_of_kept_w3sum_ac885d1
-- name    : ThreeSum.SharedReportingBankHeader.Stored.of_kept_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:00:37.7872+00:00
-- url     : https://prove2.me/theorems/e07c3cba-0942-4cd7-a619-83a0c6cc3d37
-- title:
--   Stored: of kept
-- statement:
--   The Stored construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean#L69-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean#L69-L89

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Theorems.Thm_ThreeSum_ReportingHostLevelData_Sources_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_ed168a32962ea724
import Theorems.Thm_ThreeSum_SharedReportingBankData_Entry_of_kept
import Theorems.Thm_ThreeSum_SharedReportingBankData_Tables_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_470e48753c64c7fc
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000

theorem ThreeSum.SharedReportingBankHeader.Stored.of_kept_w3sum_ac885d1 {μ ν : ℕ → ℤ} {free h J NB NC g bound : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Stored μ free h J NB NC g fB fC p shift) (heq : Kept μ ν bound)
    (hbound : finish free h J NB NC g ≤ bound) : Stored ν free h J NB NC g fB fC p shift := by sorry
