-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
-- name    : ThreeSum.LightTernaryEnumeration.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:38:26.867486+00:00
-- url     : https://prove2.me/theorems/46eada01-23ea-425f-8afc-ce9146e89096
-- title:
--   Light Ternary Enumeration: meets
-- statement:
--   The Light Ternary Enumeration construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L97-L274
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L97-L274

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.meets {pEnum W powers : ℕ}
    (hprog : P[pEnum]? = some (body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ N T pref dst : ℕ, ∀ μ : ℕ → ℤ,
      N ≤ W → T ≤ 2*W → pref+4^N ≤ 4^W →
      dst+(codes N T).length ≤ powers → Powers μ powers (2*W) →
      ∀ d, d+N ≤ lim.depth →
      Meets lim P pEnum d [N,T,pref,dst,powers] μ (time N T)
        (fun r μ' => r = ((codes N T).length : ℤ) ∧
          Seg μ' dst (output N T pref) ∧
          SameOutside μ μ' dst (codes N T).length) := by sorry
