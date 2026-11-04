-- Prove2me | Theorems.Thm_ThreeSum_LightQueryWeights_meets_w3sum_ac885d1
-- name    : ThreeSum.LightQueryWeights.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:42:18.694835+00:00
-- url     : https://prove2.me/theorems/24e180ae-aeac-4f4f-88bd-0eb191f93be1
-- title:
--   Light Query Weights: meets
-- statement:
--   The Light Query Weights construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean#L41-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryWeights.lean#L41-L144

import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryWeights
open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightQueryWeights.meets_w3sum_ac885d1 {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {W dst work d : ℕ} (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+W ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,subsetMask Q,dst,work] μ (time W)
      (fun r μ' => r = (Q.card : ℤ) ∧
        SegN μ' dst (selectedPowers Q W) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst W) := by sorry
