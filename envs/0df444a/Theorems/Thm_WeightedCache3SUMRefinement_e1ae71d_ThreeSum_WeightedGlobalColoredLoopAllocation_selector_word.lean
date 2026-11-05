-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalColoredLoopAllocation_selector_word
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation.selector_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:11:28.270792+00:00
-- url     : https://prove2.me/theorems/71d85434-06b4-45be-96d2-ada921ba2dda
-- title:
--   selector_word
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L57-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryColoredLoopAllocation.lean#L57-L73

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopAllocation
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters WeightedGlobalColoredLoopSetup
open WeightedGlobalArenaPrefixFootprints
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopAllocation.selector_word {lim : Limits} {depth : ℕ}
    (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (hA : A.length≤n)
    (hok : (WeightedGlobalArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) (j : ℕ) (hj : j<rounds P n) :
    (LightTernaryRowSelector.word (q P n*q P n)
      (numbers P.maps P.threshold P.cap P.M P.radix P.K P.H P.drift P.scale n (n^κ) (j+1)).candidateScore
      (P.p^(j+1)) (P.p^(j+1)) ((P.p^(2*P.K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2)
      (initialBudget P n A*((9*WeightedGlobalArenaBudgetExistence.pairFactor P.m P.F P.K)*
        (2^(fixedPi P.m 2*P.K)))^(j+1)) : ℤ)≤lim.word := by sorry
