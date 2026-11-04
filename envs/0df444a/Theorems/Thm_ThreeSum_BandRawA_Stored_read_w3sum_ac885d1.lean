-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_Stored_read_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.Stored.read_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:18.313954+00:00
-- url     : https://prove2.me/theorems/36ea4855-d1c6-4aad-9bce-0c9331c2606b
-- title:
--   Stored: read
-- statement:
--   The Stored construction uses the read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L135-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L135-L152

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_Light_SegN_read

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.Stored.read_w3sum_ac885d1 {μ : ℕ → ℤ} {vals owners positions n g k : ℕ}
    {rs : List Record} {f : ℕ → ℤ}
    (H : Stored μ vals owners positions f (items n g rs))
    (hk : k < (items n g rs).length) :
    μ (vals+k)=f (labelAt n g rs k).position ∧
      μ (owners+k)=((labelAt n g rs k).owner : ℤ) ∧
      μ (positions+k)=((labelAt n g rs k).position : ℤ) := by sorry
