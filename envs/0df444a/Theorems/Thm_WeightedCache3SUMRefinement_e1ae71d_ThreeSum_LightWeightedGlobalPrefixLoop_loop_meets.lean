-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixLoop_loop_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixLoop.loop_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:59:19.796866+00:00
-- url     : https://prove2.me/theorems/0cf0ad51-aa6b-4a36-8fde-dc4f33f71dee
-- title:
--   loop_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixLoop.lean#L142-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryPrefixLoop.lean#L142-L183

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixLoop
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixLoop.loop_meets {lim : Limits} {P : Program}
    {pMain rounds m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase d T : ℕ}
    (hmain : P[pMain]?=some loopBody) (μ : ℕ→ ℤ) (I : ℕ→ (ℕ→ ℤ)→ Prop)
    (hstart : I 0 μ) (hr : (rounds:ℤ)≤ lim.word) (hd : d<lim.depth)
    (hpower : ∀ j≤ rounds, ((p^j:ℕ):ℤ)≤ lim.word)
    (hstep : ∀ j<rounds, ∀ ν, I j ν→
      Meets lim P 192 (d+1)
        (stepArgs m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase j (p^j))
        ν T (fun z ξ=>z=((p^(j+1):ℕ):ℤ) ∧ I (j+1) ξ)) :
    Meets lim P pMain d
      (args rounds m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase)
      μ (time rounds T) (fun z ν=>z=((p^rounds:ℕ):ℤ) ∧ I rounds ν) := by sorry
