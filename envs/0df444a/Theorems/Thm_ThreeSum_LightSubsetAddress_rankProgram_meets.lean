-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetAddress_rankProgram_meets
-- name    : ThreeSum.LightSubsetAddress.rankProgram_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:27.174422+00:00
-- url     : https://prove2.me/theorems/0742ce90-fad7-461a-abd3-dc3d7c8784aa
-- title:
--   Light Subset Address: rank Program meets
-- statement:
--   The Light Subset Address construction uses the rank Program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetAddress.lean#L138-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetAddress.lean#L138-L147

import Definitions.Def_Submission_ThreeSum_LightPascal
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetAddress.rankProgram_meets {W table powers L k m d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (htspace : table+tableSize W ≤ lim.space)
    (hpspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : Table μ table W) (hpowers : Powers μ powers W)
    (hL : L ≤ W) (hm : IsMask L k m) (hd : d+L ≤ lim.depth) :
    Meets lim rankProgram 0 d [L,k,m,W,table,powers] μ (rankTime L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ μ' = μ) := by sorry
