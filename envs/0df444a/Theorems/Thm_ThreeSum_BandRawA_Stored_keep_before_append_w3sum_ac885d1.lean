-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_Stored_keep_before_append_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.Stored.keep_before_append_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:09.730608+00:00
-- url     : https://prove2.me/theorems/f2e58567-546d-4c60-827b-66e22d2bb8b0
-- title:
--   Stored: keep before append
-- statement:
--   The Stored construction uses the keep before append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L65-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L65-L84

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open Light BandCandidateRows
set_option maxHeartbeats 1400000

theorem ThreeSum.BandRawA.Stored.keep_before_append_w3sum_ac885d1 {μ ν : ℕ → ℤ} {vals owners positions capacity len : ℕ}
    {f : ℕ → ℤ} {ls : List Label}
    (H : Stored μ vals owners positions f ls)
    (hk : LightBandRawARow.KeptOthers μ ν (vals+ls.length) (owners+ls.length)
      (positions+ls.length) len)
    (hvals : vals+capacity ≤ owners) (howners : owners+capacity ≤ positions)
    (hfit : ls.length+len ≤ capacity) : Stored ν vals owners positions f ls := by sorry
