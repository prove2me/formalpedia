-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_program_meets
-- name    : ThreeSum.LightWeightedGlobalPrefixSetup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:51:34.853906+00:00
-- url     : https://prove2.me/theorems/a6725bda-cfab-41f2-9478-f01d46085171
-- title:
--   Light Weighted Global Prefix Setup: program meets
-- statement:
--   The Light Weighted Global Prefix Setup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L164-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixSetup.lean#L164-L172

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
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
import Theorems.Thm_ThreeSum_LightWeightedEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedGlobalPrefixSetup.program_meets {m j F dst bank work d : ℕ} (μ : ℕ→ ℤ)
    (hw : (lim.space:ℤ)≤ lim.word) (hbank : bank+nb m j≤ work)
    (hwork : work+(2*N m j+1)≤ dst) (hspace : dst+8≤ lim.space)
    (hword : (word m j F:ℤ)≤ lim.word) (hd : d+N m j+3≤ lim.depth) :
    Meets lim program 0 d [j,m,F,dst,bank,work] μ (time m j)
      (fun r ν=>r=(dst:ℤ) ∧ Seg ν dst (header m j F bank work) ∧
        Seg ν bank ((codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        Powers ν work (2*N m j) ∧ Kept μ ν bank) := by sorry
