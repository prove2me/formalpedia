-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_row_length_le
-- name    : ThreeSum.BandRawA.row_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:37.609282+00:00
-- url     : https://prove2.me/theorems/57dc597d-9238-4d4d-abfd-50bafcb4066a
-- title:
--   Band Raw A: row length le
-- statement:
--   The Band Raw A construction uses the row length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L52-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L52-L56

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.row_length_le (n g owner : ℕ) (r : Record) : (row n g owner r).length ≤ g := by sorry
