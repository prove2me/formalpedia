-- Prove2me | Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
-- name    : ThreeSum.LightQueryWeights.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:59.810859+00:00
-- url     : https://prove2.me/theorems/dd168aaf-8d7a-4ee0-8ff4-04c4d58cf9f2
-- title:
--   Light Query Weights: program meets
-- statement:
--   The Light Query Weights construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean#L148-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean#L148-L159

import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryWeights
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightQueryWeights.program_meets {μ : ℕ → ℤ} {W dst work d : ℕ}
    (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+W ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim program 0 d [W,subsetMask Q,dst,work] μ (time W)
      (fun r μ' => r = (Q.card : ℤ) ∧
        SegN μ' dst (selectedPowers Q W) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst W) := by sorry
