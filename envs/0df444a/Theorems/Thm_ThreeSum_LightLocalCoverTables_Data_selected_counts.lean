-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_selected_counts
-- name    : ThreeSum.LightLocalCoverTables.Data.selected_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:05.560197+00:00
-- url     : https://prove2.me/theorems/948fdf45-b25d-451d-b9a6-0c44e9beac28
-- title:
--   Data: selected counts
-- statement:
--   The Data construction uses the selected counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L52-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L52-L60

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

theorem ThreeSum.LightLocalCoverTables.Data.selected_counts {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    μ (hist0+candidateAt h s*localPrime h+r) =
      (HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h s) (r : LocalField h) : ℤ) ∧
    μ (hist1+candidateAt h s*localPrime h+r) =
      (HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h s) (r : LocalField h) : ℤ) := by sorry
