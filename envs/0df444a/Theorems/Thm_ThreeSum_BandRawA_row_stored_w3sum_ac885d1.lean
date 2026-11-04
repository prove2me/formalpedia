-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_row_stored_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.row_stored_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:48.340374+00:00
-- url     : https://prove2.me/theorems/826a330b-67a8-4dd3-a883-9660e6aabc38
-- title:
--   Band Raw A: row stored
-- statement:
--   The Band Raw A construction uses the row stored property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L42-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L42-L63

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open Light BandCandidateRows
set_option maxHeartbeats 1400000

theorem ThreeSum.BandRawA.row_stored_w3sum_ac885d1 {μ : ℕ → ℤ} {vals owners positions n g owner : ℕ}
    {r : Record} {f : ℕ → ℤ}
    (H : ∀ j < (row n g owner r).length,
      μ (vals+j)=f (BandPartition.start g r.a+j) ∧ μ (owners+j)=(owner : ℤ) ∧
        μ (positions+j)=((BandPartition.start g r.a+j : ℕ) : ℤ)) :
    Stored μ vals owners positions f (row n g owner r) := by sorry
