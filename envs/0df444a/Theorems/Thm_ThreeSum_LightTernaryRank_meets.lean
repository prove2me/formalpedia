-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRank_meets
-- name    : ThreeSum.LightTernaryRank.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:46.662215+00:00
-- url     : https://prove2.me/theorems/bb4cc2a9-dc8e-4052-8f41-b880ae451afd
-- title:
--   Light Ternary Rank: meets
-- statement:
--   The Light Ternary Rank construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L49-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L49-L107

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryRank.meets {pMain pDigit pErase N m powers d : ℕ}
    (hmain : P[pMain]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((2*N+16 : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hdepth : d+2*N+2 ≤ lim.depth) :
    Meets lim P pMain d [N,m,powers] μ (time N)
      (fun r ν => r=(partialRank N m N : ℤ) ∧ ν=μ) := by sorry
