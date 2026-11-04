-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_position_lt
-- name    : ThreeSum.BandRawA.position_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:36.831495+00:00
-- url     : https://prove2.me/theorems/ba74b8b6-6579-41bd-8806-caaf9cc59ac8
-- title:
--   Band Raw A: position lt
-- statement:
--   The Band Raw A construction uses the position lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L135-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L135-L138

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.position_lt {n g i : ℕ} {rs : List Record} {l : Label}
    (hl : l ∈ firstRows n g rs i) : l.position < n := by sorry
