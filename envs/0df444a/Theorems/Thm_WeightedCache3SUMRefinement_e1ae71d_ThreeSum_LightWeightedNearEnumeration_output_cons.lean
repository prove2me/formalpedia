-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedNearEnumeration_output_cons
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.output_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:08:56.785168+00:00
-- url     : https://prove2.me/theorems/8dc076df-4f83-450e-9b73-c5dbac1f971d
-- title:
--   output_cons
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightNearEnumeration.lean#L53-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightNearEnumeration.lean#L53-L67

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedNearEnumeration.output_cons (q : Fin 3) (qs : List ℕ) (D pref : ℕ) :
    output (q.val::qs) D pref = branchOutput qs D pref q.val 0 ++
      branchOutput qs D pref q.val 1 ++ branchOutput qs D pref q.val 2 := by sorry
