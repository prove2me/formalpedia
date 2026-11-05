-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_sourceArgs_length
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.sourceArgs_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:17:40.295308+00:00
-- url     : https://prove2.me/theorems/7d42f770-7fdc-42aa-944c-25c0503798de
-- title:
--   sourceArgs_length
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountHost.lean#L52-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountHost.lean#L52-L53

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.sourceArgs_length (a b c e f g h i j k l m n o p q r s t u w x y : ℕ) :
    (sourceArgs a b c e f g h i j k l m n o p q r s t u w x y).length=23 := by sorry

attribute [defeq] WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.sourceArgs_length
