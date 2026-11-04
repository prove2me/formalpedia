-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
-- name    : ThreeSum.LightWeightedNearDigits.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:18.787862+00:00
-- url     : https://prove2.me/theorems/2e0c41f5-7405-46e4-8d9f-7f0d31a89125
-- title:
--   Light Weighted Near Digits: meets
-- statement:
--   The Light Weighted Near Digits construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearDigits.lean#L38-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearDigits.lean#L38-L135

import Definitions.Def_Submission_Weighted_Enumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_Weighted_NearDigits
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryRank_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearDigits
open Light ThreeSum.LightSubsetAddress
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryJointType ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedNearDigits.meets {pMain pDigit pErase N m powers caps active d : ℕ}
    (hmain : P[pMain]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word)
    (hscalar : (1100 : ℤ)≤lim.word)
    (hm : m<2^(2*N)) (hcaps : caps+N≤active) (hactive : active+N≤powers)
    (hpowers : Powers μ powers (2*N)) (hd : d+2*N+2≤lim.depth) :
    Meets lim P pMain d [N,m,powers,caps,active] μ (time N)
      (fun _ ν => (∀ i<N, ν (caps+i)=(digitCost (LightTernaryRank.digitAt N m i) : ℤ)) ∧
        (∀ i<N, ν (active+i)=1) ∧ SameOutside μ ν caps (active+N-caps)) := by sorry
