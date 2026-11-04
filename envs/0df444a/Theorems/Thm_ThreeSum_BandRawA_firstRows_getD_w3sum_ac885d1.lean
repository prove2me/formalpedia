-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_firstRows_getD_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.firstRows_getD_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:12.077018+00:00
-- url     : https://prove2.me/theorems/3141ce73-cd21-410d-83ec-2bcba02f70a4
-- title:
--   Band Raw A: first Rows get D
-- statement:
--   The Band Raw A construction uses the first Rows get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L39-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L39-L54

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.firstRows_getD_w3sum_ac885d1 {n g s i j : ℕ} {rs : List Record}
    (hs : s < i) (hj : j < (row n g s (rs.getD s default)).length) :
    (firstRows n g rs i).getD (count n g rs s+j) default=
      ⟨s,BandPartition.start g (rs.getD s default).a+j⟩ := by sorry
