-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalTripleScan_meets_w3sum_ac885d1
-- name    : ThreeSum.LightOriginalTripleScan.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:17:43.164185+00:00
-- url     : https://prove2.me/theorems/ada23773-0744-42cb-88e0-bd207009cb27
-- title:
--   Light Original Triple Scan: meets
-- statement:
--   The Light Original Triple Scan construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalTripleScan.lean#L23-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalTripleScan.lean#L23-L71

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleRow
import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_ec604c008ed4b1df
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalTripleScan
open Light BruteTripleIndex
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOriginalTripleScan.meets_w3sum_ac885d1 {pMain pRow pDivide src n t U d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]?=some (body pMain pRow))
    (hrow : P[pRow]?=some (LightOriginalTripleRow.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (hn : 0 < n) (ht : t ≤ n^3)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : src+n ≤ lim.space)
    (hword : (LightOriginalTripleRow.word n U : ℤ) ≤ lim.word)
    (hd : d+t+2 ≤ lim.depth)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,t] μ (time n t)
      (fun result ν => (result=0 ∨ result=1) ∧ (result=1 ↔ Hit x hn t) ∧ ν=μ) := by sorry
