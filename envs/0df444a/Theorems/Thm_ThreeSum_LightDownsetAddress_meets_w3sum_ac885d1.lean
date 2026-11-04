-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetAddress_meets_w3sum_ac885d1
-- name    : ThreeSum.LightDownsetAddress.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:39.607814+00:00
-- url     : https://prove2.me/theorems/384cd5c4-f680-442f-8c38-d9766b73fee3
-- title:
--   Light Downset Address: meets
-- statement:
--   The Light Downset Address construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean#L26-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean#L26-L71

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetAddress.meets_w3sum_ac885d1 {pMain pFresh pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pFresh pOffset))
    (C : LightSubsetSetup.Procs P pFresh pBuild pFill pRow pLinear pPowers pRank)
    (hoff : P[pOffset]? = some LightSubsetOffset.body)
    {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+4 ≤ lim.depth) :
    Meets lim P pMain d [L,k,m,work] μ (time L)
      (fun r μ' => r = (downsetRank L m : ℤ) ∧ Kept μ μ' work) := by sorry
