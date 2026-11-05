-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_visits_full_succ
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.visits_full_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:59.793177+00:00
-- url     : https://prove2.me/theorems/e90d914a-72d6-43ce-8d5b-10641f7ce5c2
-- title:
--   visits_full_succ
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean#L54-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean#L54-L56

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.visits_full_succ {T : ℕ} (hT : 2740 ≤ T) (N : ℕ) :
    visits (N+1) T = 1+visits N T+visits N (T-1369)+visits N (T-2740) := by sorry
