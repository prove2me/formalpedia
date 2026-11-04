-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_counts_read
-- name    : ThreeSum.LightLocalCoverTables.Data.counts_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:44.051602+00:00
-- url     : https://prove2.me/theorems/18d07b64-d345-4cfc-8f52-eb3ca4b31103
-- title:
--   Data: counts read
-- statement:
--   The Data construction uses the counts read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L46-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L46-L50

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

theorem ThreeSum.LightLocalCoverTables.Data.counts_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < localPrime h) :
    μ (hist0+j*localPrime h+r) = (LocalCoverMatrix.leftCount (candidate h j) h r : ℤ) ∧
    μ (hist1+j*localPrime h+r) = (LocalCoverMatrix.rightCount (candidate h j) h r : ℤ) := by sorry
