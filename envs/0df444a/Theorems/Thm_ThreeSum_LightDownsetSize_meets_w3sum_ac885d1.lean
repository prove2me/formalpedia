-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetSize_meets_w3sum_ac885d1
-- name    : ThreeSum.LightDownsetSize.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:43:35.911128+00:00
-- url     : https://prove2.me/theorems/4107756a-1f88-40c2-902d-07c61174eb3f
-- title:
--   Light Downset Size: meets
-- statement:
--   The Light Downset Size construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L30-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L30-L82

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetSize.meets_w3sum_ac885d1 {pMain pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    {μ : ℕ → ℤ} {L cut work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hd : d+L+4 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,work] μ (time L)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧ Kept μ μ' work) := by sorry
