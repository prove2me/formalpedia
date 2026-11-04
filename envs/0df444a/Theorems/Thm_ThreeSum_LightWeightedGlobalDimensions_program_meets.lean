-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_program_meets
-- name    : ThreeSum.LightWeightedGlobalDimensions.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:19:27.550642+00:00
-- url     : https://prove2.me/theorems/65cefcda-559f-407b-b27d-2ebcc363fbd4
-- title:
--   Light Weighted Global Dimensions: program meets
-- statement:
--   The Light Weighted Global Dimensions construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensions.lean#L50-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensions.lean#L50-L130

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_Weighted_Global_LightTernaryDigitLength
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCandidates
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 3000000
variable {lim : Limits} {depth : ℕ}

theorem ThreeSum.LightWeightedGlobalDimensions.program_meets {M b p K n U dst : ℕ} [Fact p.Prime]
    (μ : ℕ → ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : dst+4≤lim.space)
    (hdepth : depth+1<lim.depth) (hword : (word M b p K n U : ℤ)≤lim.word) :
    Meets lim (program M b p K) 0 depth [n,U,dst] μ (time M b p K n U)
      (fun z ν => z=((p^(dim M b p K n U) : ℕ) : ℤ) ∧
        Seg ν dst [(r M n : ℤ),J M b n U,dim M b p K n U,(p^(dim M b p K n U) : ℕ)] ∧
        Kept μ ν dst) := by sorry
