-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixPhases_loop_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPhases.loop_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:11:51.546485+00:00
-- url     : https://prove2.me/theorems/c538e871-30f1-4476-a9c4-f0fea9022f04
-- title:
--   loop_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixPhases.lean#L78-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixPhases.lean#L78-L99

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixPhases
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixLoop_loop_meets

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPhases
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [instance] Phase.prime

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixPhases.loop_meets {lim : Limits} {rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
    depth K R S T : ℕ} {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ}
    (μ : ℕ→ℤ) (I : ℕ→(ℕ→ℤ)→Prop) (hstart : I 0 μ)
    (hrounds : (rounds:ℤ)≤lim.word) (hd : depth<lim.depth)
    (hpowers : ∀j≤rounds, ((p^j:ℕ):ℤ)≤lim.word)
    (X : ℕ→Inputs)
    (hargs : ∀j<rounds, (X j).argv=stepArgs m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale j (p^j))
    (hpower : ∀j<rounds, (X j).power*(X j).p=p^(j+1))
    (stages : ∀j<rounds, ∀ν,I j ν→Phase (X j) lim (depth+1) K R S p raws words maps xl yl zl xr yr zr ν)
    (hcost : ∀(j : ℕ)(hj : j<rounds), ∀ν,∀h:I j ν,(stages j hj ν h).time≤T)
    (hnext : ∀(j : ℕ)(hj : j<rounds), ∀ν,∀h:I j ν,∀ω,(stages j hj ν h).Output ω→I (j+1) ω) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 193 depth
      (args rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale)
      μ (LightWeightedGlobalPrefixLoop.time rounds T) (fun z ν=>z=((p^rounds:ℕ):ℤ) ∧ I rounds ν) := by sorry
