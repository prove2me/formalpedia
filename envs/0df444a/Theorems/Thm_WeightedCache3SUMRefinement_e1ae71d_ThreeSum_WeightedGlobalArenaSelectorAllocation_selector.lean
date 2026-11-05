-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSelectorAllocation_selector
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation.selector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:34.120283+00:00
-- url     : https://prove2.me/theorems/182e10f4-1419-40a1-903d-e409b04999b0
-- title:
--   selector
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L86-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSelectorAllocation.lean#L86-L109

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaCandidateScoreBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectorAllocation
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation
open Light WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaAllocation WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSelectorAllocation.selector {lim : Limits} {depth : ℕ}
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
