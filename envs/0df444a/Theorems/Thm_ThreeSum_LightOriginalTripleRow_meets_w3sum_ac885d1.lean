-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalTripleRow_meets_w3sum_ac885d1
-- name    : ThreeSum.LightOriginalTripleRow.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:13.401722+00:00
-- url     : https://prove2.me/theorems/910f7568-74f7-407e-8869-372acd0a2594
-- title:
--   Light Original Triple Row: meets
-- statement:
--   The Light Original Triple Row construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalTripleRow.lean#L32-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalTripleRow.lean#L32-L126

import Definitions.Def_Submission_ThreeSum_BruteTripleIndex
import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Definitions.Def_Submission_ThreeSum_LightOriginalTripleRow
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalTripleRow
open Light BruteTripleIndex
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightOriginalTripleRow.meets_w3sum_ac885d1 {pMain pDivide src n t U d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]?=some (body pDivide)) (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (hn : 0 < n) (ht : t < n^3)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : src+n ≤ lim.space)
    (hword : (word n U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hread : ∀ i : Fin n, μ (src+i.val)=x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,t] μ (time n)
      (fun result ν => (result=0 ∨ result=1) ∧
        (result=1 ↔ witness x hn ht) ∧ ν=μ) := by sorry
