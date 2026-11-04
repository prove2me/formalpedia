-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_row_getElem
-- name    : ThreeSum.BandRawA.row_getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:40.028211+00:00
-- url     : https://prove2.me/theorems/b02695a3-a64b-4c3b-90f6-a16eceb92a3e
-- title:
--   Band Raw A: row get Elem
-- statement:
--   The Band Raw A construction uses the row get Elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L58-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L58-L63

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.row_getElem {n g owner j : ℕ} {r : Record} (hj : j < (row n g owner r).length) :
    (row n g owner r)[j]=⟨owner,start g r.a+j⟩ := by sorry
