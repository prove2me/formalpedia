-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_program_meets
-- name    : ThreeSum.LightWeightedGlobalDigitLength.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:24:40.11351+00:00
-- url     : https://prove2.me/theorems/c8b4db91-dbcc-446f-a032-6a6ebc6e95d1
-- title:
--   Light Weighted Global Digit Length: program meets
-- statement:
--   The Light Weighted Global Digit Length construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDigitLength.lean#L106-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDigitLength.lean#L106-L110

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_Weighted_Global_LightTernaryDigitLength
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDigitLength
open Light WeightedGlobalSignedPadding
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightedGlobalDigitLength.program_meets {b U r : ℕ} (μ : ℕ→ℤ) (hb : 1<b) (hd : d<lim.depth)
    (hword : (word b (4*U+1)+r+4 : ℤ)≤lim.word) :
    Meets lim program 0 d [U,b,r] μ (time b U)
      (fun J ν => J=(paddedLength b U r : ℤ) ∧ ν=μ) := by sorry
