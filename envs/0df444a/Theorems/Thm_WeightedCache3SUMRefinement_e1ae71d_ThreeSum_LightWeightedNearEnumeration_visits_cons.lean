-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_visits_cons
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.visits_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:55.575795+00:00
-- url     : https://prove2.me/theorems/1c9c321d-5cd7-4a71-ab2b-741d3773af91
-- title:
--   visits_cons
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightNearEnumeration.lean#L69-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightNearEnumeration.lean#L69-L74

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.visits_cons (q : Fin 3) (qs : List ℕ) (D : ℕ) :
    visits (q.val::qs) D = 1+branchVisits qs D q.val 0+
      branchVisits qs D q.val 1+branchVisits qs D q.val 2 := by sorry
