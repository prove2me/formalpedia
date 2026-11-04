-- Prove2me | Theorems.Thm_ThreeSum_LightColorIndex_meets_w3sum_ac885d1
-- name    : ThreeSum.LightColorIndex.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:43.282848+00:00
-- url     : https://prove2.me/theorems/1e26aeed-64d7-4dea-8a1c-53965aa7de06
-- title:
--   Light Color Index: meets
-- statement:
--   The Light Color Index construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorIndex.lean#L44-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorIndex.lean#L44-L108

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightColorIndex
open Light LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightColorIndex.meets_w3sum_ac885d1 {pMain pErase W m powers d : ℕ}
    (hmain : P[pMain]? = some (body pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W) (hm : m < 2^W) (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,m,p.1.1.val,p.1.2.val,
      (p.2 (false,false)).val,(p.2 (false,true)).val,
      (p.2 (true,false)).val,(p.2 (true,true)).val,powers] μ (time W)
      (fun r μ' => r = (color p m : ℤ) ∧ μ' = μ) := by sorry
