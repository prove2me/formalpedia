-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_row_length
-- name    : ThreeSum.BandRawA.row_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:38.634769+00:00
-- url     : https://prove2.me/theorems/f9976b2e-af42-40d5-9aef-2b1b3f36044e
-- title:
--   Band Raw A: row length
-- statement:
--   The Band Raw A construction uses the row length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L47-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L47-L50

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.row_length (n g owner : ℕ) (r : Record) :
    (row n g owner r).length=if r.flag=1 then bandLength n g r.a else 0 := by sorry
