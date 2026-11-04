-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
-- name    : ThreeSum.BandRawA.Stored.of_kept
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:40.66802+00:00
-- url     : https://prove2.me/theorems/869feffc-ba64-4c07-ab80-0e506181c3fa
-- title:
--   Stored: of kept
-- statement:
--   The Stored construction uses the of kept property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L86-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L86-L93

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Theorems.Thm_Light_Seg_of_kept

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open Light BandCandidateRows
set_option maxHeartbeats 1400000

theorem ThreeSum.BandRawA.Stored.of_kept {μ ν : ℕ → ℤ} {vals owners positions fr : ℕ}
    {f : ℕ → ℤ} {ls : List Label} (H : Stored μ vals owners positions f ls)
    (hk : Kept μ ν fr) (hv : vals+ls.length ≤ fr)
    (ho : owners+ls.length ≤ fr) (hp : positions+ls.length ≤ fr) :
    Stored ν vals owners positions f ls := by sorry
