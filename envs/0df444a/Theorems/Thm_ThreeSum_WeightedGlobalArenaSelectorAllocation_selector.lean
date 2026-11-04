-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSelectorAllocation_selector
-- name    : ThreeSum.WeightedGlobalArenaSelectorAllocation.selector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:21:57.098881+00:00
-- url     : https://prove2.me/theorems/9a242d4e-c1c0-4fb3-91a0-3e2d259d91a3
-- title:
--   Weighted Global Arena Selector Allocation: selector
-- statement:
--   Every actual selector input is covered by the single fixed arena need.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L86-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L86-L109

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaSelectorAllocation.selector {lim : Limits} {depth : ℕ}
    (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (n U j nO free : ℕ) (hj : j≤Nat.clog M (n^2))
    (hO : nO≤n*2^(LightWeightedGlobalDimensions.J M b n U))
    (hok : (WeightedGlobalArenaAllocationResources.need Alloc n U).Ok lim free depth) :
    (LightTernaryRowSelector.word
      ((p^(LightWeightedGlobalDimensions.dim M b p K n U))^2)
      ((numbers maps τ cap M b K H drift scale n U j).candidateScore)
      (p^j) (p^j) ((p^(2*K))^j)
      (9^j*n^2) (9^j*n^2)
      ((drift*scale)^j*LightTernaryInitialBudgets.initial K b n
        (LightWeightedGlobalDimensions.J M b n U) nO) : ℤ)≤lim.word := by sorry
