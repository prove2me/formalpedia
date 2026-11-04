-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearDigits_meets
-- name    : ThreeSum.LightTernaryNearDigits.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:52:16.488114+00:00
-- url     : https://prove2.me/theorems/1e347f1b-a9d2-4fef-8f54-534248a32519
-- title:
--   Light Ternary Near Digits: meets
-- statement:
--   The Light Ternary Near Digits construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearDigits.lean#L30-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearDigits.lean#L30-L100

import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_Submission_ThreeSum_LightTernaryNearDigits
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryRank_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearDigits
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearDigits.meets {pMain pDigit pErase N m powers caps active d : ℕ}
    (hmain : P[pMain]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word)
    (hm : m<2^(2*N)) (hcaps : caps+N≤active) (hactive : active+N≤powers)
    (hpowers : Powers μ powers (2*N)) (hd : d+2*N+2≤lim.depth) :
    Meets lim P pMain d [N,m,powers,caps,active] μ (time N)
      (fun _ ν => (∀ i<N, ν (caps+i)=(LightTernaryRank.digitAt N m i : ℤ)) ∧
        (∀ i<N, ν (active+i)=1) ∧ SameOutside μ ν caps (active+N-caps)) := by sorry
