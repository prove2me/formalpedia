-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_count_bound
-- name    : ThreeSum.BandRawA.count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:34:32.103255+00:00
-- url     : https://prove2.me/theorems/a1c6a331-c7c8-49ca-b570-bad5b4cfe286
-- title:
--   Band Raw A: count bound
-- statement:
--   The Band Raw A construction uses the count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L83-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L83-L89

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BandCandidateRows_count_bound

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.count_bound (n g : ℕ) (rs : List Record) (i : ℕ) : count n g rs i ≤ g*i := by sorry
