-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_digits_mid
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.digits_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:56.618522+00:00
-- url     : https://prove2.me/theorems/7ba34473-1f5c-4d11-a3de-a8c4d493b859
-- title:
--   digits_mid
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean#L31-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean#L31-L32

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.digits_mid {T : ℕ} (hT : 1369 ≤ T) (hT' : T < 2740) : digits T = [0,1] := by sorry
