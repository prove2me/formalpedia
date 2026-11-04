-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
-- name    : ThreeSum.LightWeightedEnumeration.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:42:28.406178+00:00
-- url     : https://prove2.me/theorems/b227e767-ba5b-48df-8285-1324d1c0be50
-- title:
--   Light Weighted Enumeration: program meets
-- statement:
--   The Light Weighted Enumeration construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L204-L214
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L204-L214

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedEnumeration.program_meets {W powers U L k pref dst d : ℕ} {weights : ℕ → ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : (U : ℤ) ≤ lim.word)
    (hL : L ≤ W) (hk : k ≤ W+1) (hprefix : pref+total weights L ≤ U)
    (hdst : dst+L.choose k ≤ powers) (hpowers : Weights μ powers W weights)
    (hd : d+L ≤ lim.depth) :
    Meets lim program 0 d [L,k,pref,dst,powers] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        Seg μ' dst (output weights L k pref) ∧ SameOutside μ μ' dst (L.choose k)) := by sorry
