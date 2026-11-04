-- Prove2me | Theorems.Thm_ThreeSum_LightWeightRow_meets_w3sum_ac885d1
-- name    : ThreeSum.LightWeightRow.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:46.942738+00:00
-- url     : https://prove2.me/theorems/154ef8b7-2128-4c8b-be84-c60c5dcbd8fa
-- title:
--   Light Weight Row: meets
-- statement:
--   The Light Weight Row construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightRow.lean#L36-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightRow.lean#L36-L114

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightRow
open Light
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightRow.meets_w3sum_ac885d1 {pMain pDigit pDivide : ℕ}
    (hmain : P[pMain]? = some (body pDigit))
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body)
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hp : 1 ≤ p)
    (hspace : dst+n ≤ lim.space) (hpowers : powers+(W+1) ≤ lim.space)
    (hsep : Apart powers (W+1) dst n)
    (hword : (word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start+stride*i < W)
    (hread : ∀ e ≤ W, μ (powers+e) = ((p^e : ℕ) : ℤ)) :
    Meets lim P pMain d [W,p,k,powers,start,stride,dst,n] μ (time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst+i) = (WeightEnumeration.digit p W k (start+stride*i) : ℤ)) ∧
        SameOutside μ μ' dst n) := by sorry
