-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedScore_joint_meets
-- name    : ThreeSum.LightWeightedScore.joint_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:28.295036+00:00
-- url     : https://prove2.me/theorems/d4f05528-18d4-4175-94d5-cfc45c522faf
-- title:
--   Light Weighted Score: joint meets
-- statement:
--   The Light Weighted Score construction uses the joint meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedScore.lean#L33-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightedScore.lean#L33-L78

import Definitions.Def_Submission_ThreeSum_WeightedScore
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightWeightedScore
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedScore
open Light WeightedModuli WeightedScore LightResidues
variable {lim : Limits} {P : Program} {d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightWeightedScore.joint_meets {pJoint pEmod : ℕ}
    (hjoint : P[pJoint]? = some (jointBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {q p maxMod free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hq : 0 < q) (hp : 0 < p) (hmax : q*p ≤ maxMod)
    (hspace : free + (Nat.log 2 (maxMod+1)+2) ≤ lim.space)
    (hword : (8*maxMod+16 : ℕ) ≤ lim.word) :
    Meets lim P pJoint d [q,p,free] μ (jointTime maxMod)
      fun r μ' => r = (joint q p : ℤ) ∧ Kept μ μ' free := by sorry
