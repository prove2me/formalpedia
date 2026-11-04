-- Prove2me | Theorems.Thm_ThreeSum_LightRadixKeys_meets_w3sum_ac885d1
-- name    : ThreeSum.LightRadixKeys.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:25.461426+00:00
-- url     : https://prove2.me/theorems/761b34a9-6afc-4122-bbab-bfb8124cd503
-- title:
--   Light Radix Keys: meets
-- statement:
--   The Light Radix Keys construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L97-L199
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRadixKeys.lean#L97-L199

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightReportingAffine_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightRadixKeys.meets_w3sum_ac885d1 {pMain pRows pAffine src dst p U : ℕ}
    (hmain : P[pMain]? = some (body pMain pRows))
    (hrows : P[pRows]? = some (LightRadixRows.body pAffine))
    (haffine : P[pAffine]? = some LightReportingAffine.body)
    (base : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+base.length ≤ dst) (hm : 0 < base.length)
    (hbound : ∀ x ∈ base, |x| ≤ (U : ℤ)) :
    ∀ J d : ℕ, ∀ μ : ℕ → ℤ,
      space dst base.length J ≤ lim.space → (word p U J : ℤ) ≤ lim.word →
      d+J+2 ≤ lim.depth → Seg μ src base →
      Meets lim P pMain d [src,base.length,J,p,dst] μ (time base.length J)
        (fun r ν => r = ((dst+offset base.length J : ℕ) : ℤ) ∧
          ν (dst+offset base.length J) = ((base.length^J : ℕ) : ℤ) ∧
          Seg ν (dst+offset base.length J+1) (values (p : ℤ) base J) ∧ Kept μ ν dst) := by sorry
