-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCodes_digit_meets
-- name    : ThreeSum.LightTernaryCodes.digit_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:36:08.106923+00:00
-- url     : https://prove2.me/theorems/5fe7d668-174d-4174-ab05-41c7c3d9d942
-- title:
--   Light Ternary Codes: digit meets
-- statement:
--   The Light Ternary Codes construction uses the digit meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCodes.lean#L70-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCodes.lean#L70-L119

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCodes
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryCodes.digit_meets {pMain pErase W low high m powers d : ℕ}
    (hmain : P[pMain]? = some (digitBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W)
    (hlow : low ≤ W) (hhigh : high ≤ W) (hm : m < 2^W)
    (hd : d+W+1 ≤ lim.depth) (htwo : 2 ≤ lim.word) :
    Meets lim P pMain d [W,low,high,m,powers] μ (digitTime W)
      (fun r μ' => r = (digit W low high m : ℤ) ∧ μ' = μ) := by sorry
