-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
-- name    : ThreeSum.LightSubsetSetup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:38.9312+00:00
-- url     : https://prove2.me/theorems/dab920b7-673d-4e02-82b5-228f635f1220
-- title:
--   Light Subset Setup: program meets
-- statement:
--   The Light Subset Setup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetSetup.lean#L87-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetSetup.lean#L87-L95

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetSetup.program_meets {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+3 ≤ lim.depth) :
    Meets lim program 0 d [L,k,m,work] μ (time L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ Table μ' work L ∧
        Powers μ' (work+tableSize L) L ∧ Kept μ μ' work) := by sorry
