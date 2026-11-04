-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_matrix_read
-- name    : ThreeSum.LightLocalCoverTables.Data.matrix_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:19.419455+00:00
-- url     : https://prove2.me/theorems/46536490-748b-4047-a02b-d5e490672741
-- title:
--   Data: matrix read
-- statement:
--   The Data construction uses the matrix read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L42-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L42-L44

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

theorem ThreeSum.LightLocalCoverTables.Data.matrix_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < cols h) :
    μ (matrixPtr+j*cols h+r) = (matrix h j r : ℤ) := by sorry
