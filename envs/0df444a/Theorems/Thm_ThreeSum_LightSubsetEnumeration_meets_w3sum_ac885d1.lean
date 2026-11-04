-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetEnumeration_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSubsetEnumeration.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:40.18832+00:00
-- url     : https://prove2.me/theorems/9890627f-ef2a-431f-880f-556422cdf4af
-- title:
--   Light Subset Enumeration: meets
-- statement:
--   The Light Subset Enumeration construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumeration.lean#L65-L203
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumeration.lean#L65-L203

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetEnumeration.meets_w3sum_ac885d1 {pEnum W powers : ℕ}
    (hprog : P[pEnum]? = some (body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ L k pref dst : ℕ, ∀ μ : ℕ → ℤ,
      L ≤ W → k ≤ W+1 → pref+2^L ≤ 2^W →
      dst+L.choose k ≤ powers → Powers μ powers W →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pEnum d [L,k,pref,dst,powers] μ (time L k)
        (fun r μ' => r = (L.choose k : ℤ) ∧
          Seg μ' dst (output L k pref) ∧ SameOutside μ μ' dst (L.choose k)) := by sorry
