-- Prove2me | Theorems.Thm_ThreeSum_LightColorArray_meets_w3sum_ac885d1
-- name    : ThreeSum.LightColorArray.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:37:58.364275+00:00
-- url     : https://prove2.me/theorems/5df85c9b-de0f-479d-9a28-fae83dad55b1
-- title:
--   Light Color Array: meets
-- statement:
--   The Light Color Array construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorArray.lean#L37-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorArray.lean#L37-L99

import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightColorArray
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorArray
open Light LightSubsetAddress
set_option maxHeartbeats 1200000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightColorArray.meets_w3sum_ac885d1 {pMain pPowers pColor pErase W n dst work : ℕ}
    (hmain : P[pMain]? = some (body pPowers pColor))
    (hpowers : P[pPowers]? = some powTableBody)
    (hcolor : P[pColor]? = some (LightColorIndex.body pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hdst : dst+n ≤ work) (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hd : d+W+2 ≤ lim.depth) :
    Meets lim P pMain d [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,dst,work]
      μ (time W n) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightColorIndex.color p i : ℤ)) ∧
        Powers ν work W ∧ KeptBut μ ν work dst n) := by sorry
