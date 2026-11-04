-- Prove2me | Theorems.Thm_ThreeSum_LightMaskErase_meets_w3sum_ac885d1
-- name    : ThreeSum.LightMaskErase.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:59.120206+00:00
-- url     : https://prove2.me/theorems/eb74c84c-b845-44fd-afc8-a14c0bbe57fe
-- title:
--   Light Mask Erase: meets
-- statement:
--   The Light Mask Erase construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskErase.lean#L32-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskErase.lean#L32-L99

import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightMaskErase
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskErase
open Light ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightMaskErase.meets_w3sum_ac885d1 {pErase W powers : ℕ} (hprog : P[pErase]? = some (body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W) :
    ∀ L a m : ℕ, L ≤ W → a ≤ W → m < 2^L →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pErase d [L,a,m,W,powers] μ (time L)
        (fun r μ' => r = (eraseMask L a m : ℤ) ∧ μ' = μ) := by sorry
