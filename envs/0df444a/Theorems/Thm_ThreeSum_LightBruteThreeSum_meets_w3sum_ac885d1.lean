-- Prove2me | Theorems.Thm_ThreeSum_LightBruteThreeSum_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBruteThreeSum.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:25:58.21705+00:00
-- url     : https://prove2.me/theorems/9813cc7f-a9fc-4ef2-81cd-1dcbb946bfe6
-- title:
--   Light Brute Three Sum: meets
-- statement:
--   The Light Brute Three Sum construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBruteThreeSum.lean#L36-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBruteThreeSum.lean#L36-L63

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_ec604c008ed4b1df
import Definitions.Def_WeightedCache3SUM_Alias_eb09b223848624eb
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightBruteThreeSum
open Light ThreeSumApsp.Spec
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBruteThreeSum.meets_w3sum_ac885d1 {pMain pScan pRow pDivide src n U fr d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]?=some (body pScan))
    (hscan : P[pScan]?=some (LightOriginalTripleScan.body pScan pRow))
    (hrow : P[pRow]?=some (LightOriginalTripleRow.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (hn : 0 < n) (hsrc : src+n ≤ fr) (H : (need n U).Ok lim fr d)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [n,U,src,fr] μ (time n)
      (fun r ν => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ ν=μ) := by sorry
