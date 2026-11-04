-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_Stored_append
-- name    : ThreeSum.BandRawA.Stored.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:29:10.246832+00:00
-- url     : https://prove2.me/theorems/bd9c0386-d820-4760-bc0b-7fca73d34cb5
-- title:
--   Stored: append
-- statement:
--   The Stored construction uses the append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L21-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAMemory.lean#L21-L31

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open Light BandCandidateRows
set_option maxHeartbeats 1400000

theorem ThreeSum.BandRawA.Stored.append {μ : ℕ → ℤ} {vals owners positions : ℕ} {f : ℕ → ℤ} {as bs : List Label}
    (H : Stored μ vals owners positions f as)
    (K : Stored μ (vals+as.length) (owners+as.length) (positions+as.length) f bs) :
    Stored μ vals owners positions f (as++bs) := by sorry
