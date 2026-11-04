-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRankTable_meets_words
-- name    : ThreeSum.LightTernaryRankTable.meets_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:00.359831+00:00
-- url     : https://prove2.me/theorems/663fa9fd-6fe3-4cc4-8280-11a12deaf65c
-- title:
--   Light Ternary Rank Table: meets words
-- statement:
--   In particular, the constructed table contains actual word ranks.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRankTable.lean#L97-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRankTable.lean#L97-L117

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRankTable
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType
  ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryRankTable.meets_words {pMain pRank pDigit pErase N a n powers dst d : ℕ}
    (hmain : P[pMain]?=some (body pRank))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (words : ℕ → TritWord N)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ dst) (hp : powers+(2*N+1) ≤ dst)
    (hdst : dst+n ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (a+j)=(address (words j) : ℤ))
    (hpowers : Powers μ powers (2*N))
    (hdepth : d+2*N+3 ≤ lim.depth) :
    Meets lim P pMain d [N,a,n,powers,dst] μ (time N n)
      (fun _ ν => (∀ j < n, ν (dst+j)=(rank (words j) : ℤ)) ∧
        SameOutside μ ν dst n) := by sorry
