-- Prove2me | Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
-- name    : ThreeSum.LightCacheEnumeration.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:38:37.817087+00:00
-- url     : https://prove2.me/theorems/7314a05c-8b04-4110-9c36-362b4a2d17b7
-- title:
--   Light Cache Enumeration: meets
-- statement:
--   The Light Cache Enumeration construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L108-L269
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L108-L269

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_LightEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7

set_option autoImplicit false
open ThreeSum ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightCacheEnumeration.meets {pEnum W powers : ℕ}
    (hprog : P[pEnum]? = some (body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((1025*W+1100 : ℕ) : ℤ) ≤ lim.word) :
    ∀ N T pref dst : ℕ, ∀ μ : ℕ → ℤ,
      N ≤ W → T ≤ 1025*W → pref+4^N ≤ 4^W →
      dst+(codes N T).length ≤ powers → Powers μ powers (2*W) →
      ∀ d, d+N ≤ lim.depth →
      Meets lim P pEnum d [N,T,pref,dst,powers] μ (time N T)
        (fun r μ' => r = ((codes N T).length : ℤ) ∧
          Seg μ' dst (output N T pref) ∧
          SameOutside μ μ' dst (codes N T).length) := by sorry
