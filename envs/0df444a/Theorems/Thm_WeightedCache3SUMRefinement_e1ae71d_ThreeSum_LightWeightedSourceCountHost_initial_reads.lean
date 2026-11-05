-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_initial_reads
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.initial_reads
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:18:09.510178+00:00
-- url     : https://prove2.me/theorems/9f7036e1-06f7-4ac2-96db-bdf816b32ccc
-- title:
--   initial_reads
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountHost.lean#L103-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/SourceCountHost.lean#L103-L122

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedSourceCountHost.initial_reads (left right frontend : List ℤ)
    (hl : left.length=23) (hr : right.length=23) :
    Reads (frame (args left right frontend)) 0 left ∧
    Reads (frame (args left right frontend)) 23 right ∧
    Reads (frame (args left right frontend)) 46 frontend := by sorry
