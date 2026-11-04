-- Prove2me | Theorems.Thm_ThreeSum_LightMaskBits_program_meets
-- name    : ThreeSum.LightMaskBits.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:25:29.619522+00:00
-- url     : https://prove2.me/theorems/712ddafc-c289-4742-ad9b-27d9b96f3e64
-- title:
--   Light Mask Bits: program meets
-- statement:
--   The Light Mask Bits construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBits.lean#L117-L125
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBits.lean#L117-L125

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBits
open Light LightSubsetAddress MaskErase
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightMaskBits.program_meets
    {μ : ℕ → ℤ} {L m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space) (hdst : dst+L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) (hm : m < 2^L) :
    Meets lim program 0 d [L,m,dst,work] μ (time L)
      (fun _ μ' => (∀ j < L, μ' (dst+j) = (bit L m j : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst L) := by sorry
