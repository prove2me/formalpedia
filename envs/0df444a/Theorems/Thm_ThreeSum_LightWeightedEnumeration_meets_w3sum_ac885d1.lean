-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEnumeration_meets_w3sum_ac885d1
-- name    : ThreeSum.LightWeightedEnumeration.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:13:31.732316+00:00
-- url     : https://prove2.me/theorems/17b723da-c095-46e5-9bba-3d45b85f7a4d
-- title:
--   Light Weighted Enumeration: meets
-- statement:
--   The Light Weighted Enumeration construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L66-L200
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedEnumeration.lean#L66-L200

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightedEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open LightSubsetEnumeration (time work_pos)
open scoped BigOperators
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedEnumeration.meets_w3sum_ac885d1 {pEnum W powers U : ℕ} {weights : ℕ → ℕ}
    (hprog : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : (U : ℤ) ≤ lim.word) :
    ∀ L k pref dst : ℕ, ∀ μ : ℕ → ℤ,
      L ≤ W → k ≤ W+1 → pref+total weights L ≤ U →
      dst+L.choose k ≤ powers → Weights μ powers W weights →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pEnum d [L,k,pref,dst,powers] μ (time L k)
        (fun r μ' => r = (L.choose k : ℤ) ∧
          Seg μ' dst (output weights L k pref) ∧ SameOutside μ μ' dst (L.choose k)) := by sorry
