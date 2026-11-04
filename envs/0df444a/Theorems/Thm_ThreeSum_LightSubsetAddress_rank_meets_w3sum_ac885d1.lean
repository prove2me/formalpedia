-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetAddress_rank_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSubsetAddress.rank_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:58.265358+00:00
-- url     : https://prove2.me/theorems/4ef21904-deef-4aa3-83d9-bf871fec0363
-- title:
--   Light Subset Address: rank meets
-- statement:
--   The Light Subset Address construction uses the rank meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetAddress.lean#L49-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetAddress.lean#L49-L134

import Definitions.Def_Submission_ThreeSum_LightPascal
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetAddress.rank_meets_w3sum_ac885d1 {pRank W table powers : ℕ}
    (hprog : P[pRank]? = some (rankBody pRank)) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (htspace : table+tableSize W ≤ lim.space)
    (hpspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : Table μ table W) (hpowers : Powers μ powers W) :
    ∀ L k m : ℕ, L ≤ W → IsMask L k m →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pRank d [L,k,m,W,table,powers] μ (rankTime L)
        (fun r μ' => r = (layerRank L k m : ℤ) ∧ μ' = μ) := by sorry
