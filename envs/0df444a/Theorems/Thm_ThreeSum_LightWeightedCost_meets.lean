-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedCost_meets
-- name    : ThreeSum.LightWeightedCost.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:52.710577+00:00
-- url     : https://prove2.me/theorems/214f0bfa-60c5-4e60-b220-8d36175c3821
-- title:
--   Light Weighted Cost: meets
-- statement:
--   The Light Weighted Cost construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean#L62-L130
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightCost.lean#L62-L130

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_Weighted_LightCost
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedCost
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
open ThreeSum.WeightedEnumeration
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedCost.meets {pMain pDigit pErase N m powers d : ℕ}
    (hmain : P[pMain]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hscalar : ((1025*N+1100 : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hdepth : d+2*N+2 ≤ lim.depth) :
    Meets lim P pMain d [N,m,powers] μ (time N)
      (fun r ν => r=(partialCost N m N : ℤ) ∧ ν=μ) := by sorry
