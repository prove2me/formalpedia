-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_values_getD_owner
-- name    : ThreeSum.BandRawA.values_getD_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:12.53787+00:00
-- url     : https://prove2.me/theorems/08cc2cd6-55b6-4caa-b9f0-fef0e21390e8
-- title:
--   Band Raw A: values get D owner
-- statement:
--   The Band Raw A construction uses the values get D owner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L129-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAIndex.lean#L129-L133

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.values_getD_owner {n g s j : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    (values f (items n g rs)).getD (count n g rs s+j) 0=
      f (BandPartition.start g (rs.getD s default).a+j) := by sorry
