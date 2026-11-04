-- Prove2me | Theorems.Thm_ThreeSum_LightQueryEnumeration_meets_w3sum_ac885d1
-- name    : ThreeSum.LightQueryEnumeration.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:03:36.016876+00:00
-- url     : https://prove2.me/theorems/6afb562d-c84f-4136-8c43-f81da84bc44e
-- title:
--   Light Query Enumeration: meets
-- statement:
--   The Light Query Enumeration construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryEnumeration.lean#L26-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryEnumeration.lean#L26-L71

import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_874c626a95c648fa
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_faf0bf412734022a

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightQueryEnumeration.meets_w3sum_ac885d1 {pMain pWeights pPowers pErase pEnum : ℕ}
    (hmain : P[pMain]? = some (body pWeights pEnum))
    (hweights : P[pWeights]? = some (LightQueryWeights.body pPowers pErase))
    (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {W t dst work d : ℕ} (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdst : dst+Q.card.choose t ≤ work)
    (hd : d+W+2 ≤ lim.depth) :
    Meets lim P pMain d [W,subsetMask Q,t,dst,work] μ (time W Q.card t)
      (fun r μ' => r = (Q.card.choose t : ℤ) ∧
        SegN μ' dst ((missingSets Q t).map subsetMask) ∧
        LightWeightedEnumeration.Weights μ' work Q.card (weights Q) ∧
        KeptBut μ μ' work dst (Q.card.choose t)) := by sorry
