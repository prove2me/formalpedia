-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCodes_zero_meets
-- name    : ThreeSum.LightTernaryCodes.zero_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:36:16.112347+00:00
-- url     : https://prove2.me/theorems/9d2e4db7-0f8f-4bbd-a3ae-50e3f0654c47
-- title:
--   Light Ternary Codes: zero meets
-- statement:
--   The Light Ternary Codes construction uses the zero meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCodes.lean#L37-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCodes.lean#L37-L58

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCodes
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryCodes.zero_meets {pMain pErase W low high m powers d : ℕ}
    (hmain : P[pMain]? = some (zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W)
    (hlow : low ≤ W) (hhigh : high ≤ W) (hm : m < 2^W)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,low,high,m,powers] μ (zeroTime W)
      (fun r μ' => r = (zeroCode W low high m : ℤ) ∧ μ' = μ) := by sorry
