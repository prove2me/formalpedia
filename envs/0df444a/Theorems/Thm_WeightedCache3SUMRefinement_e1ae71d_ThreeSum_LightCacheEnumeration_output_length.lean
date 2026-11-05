-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightCacheEnumeration_output_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:56.959884+00:00
-- url     : https://prove2.me/theorems/fc6332d2-7dea-4efb-87b4-27757f46a7a5
-- title:
--   output_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean#L23-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/LightEnumeration.lean#L23-L24

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightCacheEnumeration.output_length (N T pref : ℕ) :
    (output N T pref).length = (codes N T).length := by sorry
