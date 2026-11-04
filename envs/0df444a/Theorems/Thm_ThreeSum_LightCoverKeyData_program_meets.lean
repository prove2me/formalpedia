-- Prove2me | Theorems.Thm_ThreeSum_LightCoverKeyData_program_meets
-- name    : ThreeSum.LightCoverKeyData.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:25:48.898291+00:00
-- url     : https://prove2.me/theorems/16c5b4b7-c858-45a0-bce3-d7c81e27ec62
-- title:
--   Light Cover Key Data: program meets
-- statement:
--   The Light Cover Key Data construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L79-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverKeyData.lean#L79-L86

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoverGreedy_program_meets
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
import Theorems.Thm_ThreeSum_LightCoverUpdate_program_meets
import Theorems.Thm_ThreeSum_LightLocalCounts_program_meets
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_program_meets
import Theorems.Thm_ThreeSum_LightLocalParameters_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightPairFlags_program_meets
import Theorems.Thm_ThreeSum_LightPrimality_program_meets
import Theorems.Thm_ThreeSum_LightPrimePool_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSelectedPrime_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightDecode_program_meets
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

theorem ThreeSum.LightCoverKeyData.program_meets {lim : Limits} {μ : ℕ → ℤ} {h J free d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : LightCoverKeys.space free h J ≤ lim.space)
    (hword : (LightCoverKeys.word h J : ℤ) ≤ lim.word) :
    Meets lim LightCoverKeys.program 67 d [h,J,free] μ (LightCoverKeys.time h J)
      (fun r ν => r=(LightCoverKeys.keyHeader free h J : ℤ) ∧ Stored ν free h J ∧ Kept μ ν free) := by sorry
