-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_loop_meets
-- name    : ThreeSum.LightWeightedGlobalPrefixLoop.loop_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:33:58.895882+00:00
-- url     : https://prove2.me/theorems/80d0a744-d388-47b1-a992-e7ed1034865b
-- title:
--   Light Weighted Global Prefix Loop: loop meets
-- statement:
--   Phase interface for the actual fixed outer loop. The concrete step is
--   entry180 above, not an externally supplied procedure. Its execution receipt
--   is discharged by the source/score/span factories in the whole controller.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixLoop.lean#L142-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixLoop.lean#L142-L183

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernarySeedController
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitSpan
import Definitions.Def_Submission_ThreeSum_LightTernaryRepeatWord
import Definitions.Def_Submission_ThreeSum_LightTernaryBudgetStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixLoop
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixLoop
open Light
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixLoop.loop_meets {lim : Limits} {P : Program}
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
