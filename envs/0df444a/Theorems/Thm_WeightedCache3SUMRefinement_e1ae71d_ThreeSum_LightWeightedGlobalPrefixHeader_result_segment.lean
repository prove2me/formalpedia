-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalPrefixHeader_result_segment
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader.result_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:06:27.23503+00:00
-- url     : https://prove2.me/theorems/2fee8ce7-c8ea-467e-9e1b-a8c8e1f4eb37
-- title:
--   result_segment
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L56-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrefixHeaderSegment.lean#L56-L70

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixHeader
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrefixHeaderSegment
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_Reads_update

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader
open Light
set_option maxHeartbeats 4000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixHeader.result_segment {μ μ₀ ν : ℕ→ℤ} {template live hdr s m p power alpha2 alphaRank localQ radix J
    N T L groups nb bank powers Fbase Gbase : ℕ} {ret : ℤ} {xs : List ℤ}
    (hlen : xs.length=106) (hxs : Seg μ template xs)
    (hcopy : ∀i<106, μ₀ (live+i)=μ (template+i))
    (hν : ν=Function.update (patch live
      (frame (args template live hdr s m p power alpha2 alphaRank localQ radix J++
        locals N T L groups nb bank powers s p power alpha2 alphaRank localQ radix Fbase Gbase++[ret]))
      μ₀ LightWeightedGlobalPrefixLoop.headerWrites) (live+104) 0) :
    Seg ν live (resultHeader xs template live hdr s m p power alpha2 alphaRank localQ radix J
      N T L groups nb bank powers Fbase Gbase ret) := by sorry
