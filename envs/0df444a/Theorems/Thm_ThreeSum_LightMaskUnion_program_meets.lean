-- Prove2me | Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
-- name    : ThreeSum.LightMaskUnion.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:25:28.804047+00:00
-- url     : https://prove2.me/theorems/432aaace-2f99-406a-901b-5fc36ef46f58
-- title:
--   Light Mask Union: program meets
-- statement:
--   The Light Mask Union construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskUnion.lean#L165-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskUnion.lean#L165-L175

import Definitions.Def_Submission_ThreeSum_MaskUnion
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskUnion
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightMaskUnion.program_meets {μ : ℕ → ℤ} {W dst work d : ℕ} (A B : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+1 ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim program 0 d [W,A.card,subsetMask A,subsetMask B,dst,work] μ (time W)
      (fun r μ' => r = (subsetMask (A ∪ B) : ℤ) ∧
        μ' dst = ((A ∪ B).card : ℤ) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst 1) := by sorry
