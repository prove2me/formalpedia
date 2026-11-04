-- Prove2me | Theorems.Thm_ThreeSum_LightMaskUnion_meets_w3sum_ac885d1
-- name    : ThreeSum.LightMaskUnion.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:20.743051+00:00
-- url     : https://prove2.me/theorems/036f50fc-ad9f-4d57-9a57-8db90edf302e
-- title:
--   Light Mask Union: meets
-- statement:
--   The Light Mask Union construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskUnion.lean#L46-L161
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskUnion.lean#L46-L161

import Definitions.Def_Submission_ThreeSum_MaskUnion
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskUnion
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightMaskUnion.meets_w3sum_ac885d1 {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {W dst work d : ℕ} (A B : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+1 ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,A.card,subsetMask A,subsetMask B,dst,work] μ (time W)
      (fun r μ' => r = (subsetMask (A ∪ B) : ℤ) ∧
        μ' dst = ((A ∪ B).card : ℤ) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst 1) := by sorry
