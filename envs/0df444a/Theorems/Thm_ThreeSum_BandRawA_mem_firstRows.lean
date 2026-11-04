-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_firstRows
-- name    : ThreeSum.BandRawA.mem_firstRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:39.222443+00:00
-- url     : https://prove2.me/theorems/ff077cf6-3147-4455-8a9d-f6954fd8b648
-- title:
--   Band Raw A: mem first Rows
-- statement:
--   The Band Raw A construction uses the mem first Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L123-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L123-L133

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by sorry
