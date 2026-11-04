-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_of_kept_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverTables.Data.of_kept_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:25:37.439205+00:00
-- url     : https://prove2.me/theorems/8f47b7cb-b226-4a9e-9622-82d8dd22c318
-- title:
--   Data: of kept
-- statement:
--   The Data construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L62-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverTables.lean#L62-L84

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

theorem ThreeSum.LightLocalCoverTables.Data.of_kept_w3sum_ac885d1 {μ ν : ℕ → ℤ} {h maps hist0 hist1 matrixPtr cut : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) (K : Kept μ ν cut)
    (hmaps : maps+rows h*(2*(512*h)) ≤ cut)
    (hhist0 : hist0+rows h*localPrime h ≤ cut)
    (hhist1 : hist1+rows h*localPrime h ≤ cut)
    (hmatrix : matrixPtr+rows h*cols h ≤ cut) : Data ν h maps hist0 hist1 matrixPtr := by sorry
