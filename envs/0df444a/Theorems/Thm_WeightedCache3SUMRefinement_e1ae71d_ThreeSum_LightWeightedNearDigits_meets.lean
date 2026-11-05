-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearDigits_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearDigits.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:32.081012+00:00
-- url     : https://prove2.me/theorems/1bc24ab9-a54c-40fc-8961-9ffada3c0632
-- title:
--   meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearDigits.lean#L38-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/NearDigits.lean#L38-L135

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearDigits
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightTernaryRank_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearDigits
open Light ThreeSum.LightSubsetAddress
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryJointType ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearDigits.meets {pMain pDigit pErase N m powers caps active d : ℕ}
    (hmain : P[pMain]?=some (body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word)
    (hscalar : (3000 : ℤ)≤lim.word)
    (hm : m<2^(2*N)) (hcaps : caps+N≤active) (hactive : active+N≤powers)
    (hpowers : Powers μ powers (2*N)) (hd : d+2*N+2≤lim.depth) :
    Meets lim P pMain d [N,m,powers,caps,active] μ (time N)
      (fun _ ν => (∀ i<N, ν (caps+i)=(digitCost (LightTernaryRank.digitAt N m i) : ℤ)) ∧
        (∀ i<N, ν (active+i)=1) ∧ SameOutside μ ν caps (active+N-caps)) := by sorry
