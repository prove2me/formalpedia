-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetOffset_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSubsetOffset.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:11.811636+00:00
-- url     : https://prove2.me/theorems/31b4fd9d-b821-49e3-9d07-63dc21c76f40
-- title:
--   Light Subset Offset: meets
-- statement:
--   The Light Subset Offset construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetOffset.lean#L27-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetOffset.lean#L27-L81

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetOffset
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSubsetOffset.meets_w3sum_ac885d1 {pOffset table W L k : ℕ}
    (hprog : P[pOffset]? = some body) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : table+tableSize W ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : Table μ table W) (hL : L ≤ W) (hk : k ≤ W) :
    Meets lim P pOffset d [table,L,k,W] μ (time k)
      (fun r μ' => r = (layerOffset L k : ℤ) ∧ μ' = μ) := by sorry
