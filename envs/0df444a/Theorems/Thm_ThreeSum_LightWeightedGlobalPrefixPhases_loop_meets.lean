-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixPhases_loop_meets
-- name    : ThreeSum.LightWeightedGlobalPrefixPhases.loop_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:59:57.445841+00:00
-- url     : https://prove2.me/theorems/c8643ef7-1d3e-4c4e-a6b0-543cdea4a6b2
-- title:
--   Light Weighted Global Prefix Phases: loop meets
-- statement:
--   The actual fixed loop is derived from pure certificates for each phase.
--   There is no arbitrary execution callback in this interface.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixPhases.lean#L78-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixPhases.lean#L78-L99

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixStep
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixPhases
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixLoop_loop_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixPhases
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixLoop
open LightWeightedGlobalPrefixStep
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [instance] Phase.prime

theorem ThreeSum.LightWeightedGlobalPrefixPhases.loop_meets {lim : Limits} {rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
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
