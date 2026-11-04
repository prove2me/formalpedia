-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalColoredLoopAllocation_selector_word
-- name    : ThreeSum.WeightedGlobalColoredLoopAllocation.selector_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T02:19:23.957446+00:00
-- url     : https://prove2.me/theorems/4ccbc11e-2f1c-4469-86bb-414b8ee16ba9
-- title:
--   Weighted Global Colored Loop Allocation: selector word
-- statement:
--   The real selector's cross products are covered by the fourth-power
--   allocation envelope, using the exact six compiled threshold values.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L57-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L57-L73

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem ThreeSum.WeightedGlobalColoredLoopAllocation.selector_word {lim : Limits} {depth : ℕ}
    (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (hA : A.length≤n)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) (j : ℕ) (hj : j<rounds P n) :
    (LightTernaryRowSelector.word (q P n*q P n)
      (numbers P.maps P.threshold P.cap P.M P.radix P.K P.H P.drift P.scale n (n^κ) (j+1)).candidateScore
      (P.p^(j+1)) (P.p^(j+1)) ((P.p^(2*P.K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2)
      (initialBudget P n A*((9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K)*
        (2^(fixedPi P.m 2*P.K)))^(j+1)) : ℤ)≤lim.word := by sorry
