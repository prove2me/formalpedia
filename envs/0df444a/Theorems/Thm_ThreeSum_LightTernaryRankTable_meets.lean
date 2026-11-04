-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
-- name    : ThreeSum.LightTernaryRankTable.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:14.386666+00:00
-- url     : https://prove2.me/theorems/4dffb9b0-c0ee-4de4-b236-993a8c3f4c90
-- title:
--   Light Ternary Rank Table: meets
-- statement:
--   The Light Ternary Rank Table construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRankTable.lean#L33-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRankTable.lean#L33-L94

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_ThreeSum_LightTernaryPass
import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRankTable
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType
  ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryRankTable.meets {pMain pRank pDigit pErase N a n powers dst d : ℕ}
    (hmain : P[pMain]?=some (body pRank))
    (hrank : P[pRank]?=some (LightTernaryRank.body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (codes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ dst) (hp : powers+(2*N+1) ≤ dst)
    (hdst : dst+n ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (a+j)=(codes j : ℤ))
    (hpowers : Powers μ powers (2*N))
    (hcodes : ∀ j < n, codes j < 2^(2*N))
    (hdepth : d+2*N+3 ≤ lim.depth) :
    Meets lim P pMain d [N,a,n,powers,dst] μ (time N n)
      (fun _ ν => (∀ j < n, ν (dst+j)=values N codes j) ∧
        SameOutside μ ν dst n) := by sorry
