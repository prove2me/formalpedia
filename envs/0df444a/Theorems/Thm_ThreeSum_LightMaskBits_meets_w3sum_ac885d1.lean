-- Prove2me | Theorems.Thm_ThreeSum_LightMaskBits_meets_w3sum_ac885d1
-- name    : ThreeSum.LightMaskBits.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:22:30.602988+00:00
-- url     : https://prove2.me/theorems/6a4474f8-e0a7-4ad1-90af-521e52800c62
-- title:
--   Light Mask Bits: meets
-- statement:
--   The Light Mask Bits construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBits.lean#L42-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBits.lean#L42-L113

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBits
open Light LightSubsetAddress MaskErase
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightMaskBits.meets_w3sum_ac885d1 {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space) (hdst : dst+L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) (hm : m < 2^L) :
    Meets lim P pMain d [L,m,dst,work] μ (time L)
      (fun _ μ' => (∀ j < L, μ' (dst+j) = (bit L m j : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst L) := by sorry
