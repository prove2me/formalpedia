-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_row_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.mem_row_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:59.978867+00:00
-- url     : https://prove2.me/theorems/32bfaac9-d0f7-4908-b528-77bdc7030b20
-- title:
--   Band Raw A: mem row
-- statement:
--   The Band Raw A construction uses the mem row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L98-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L98-L121

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_BlockRows_mem_row
attribute [local simp] ThreeSum.BlockRows.mem_row


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.mem_row_w3sum_ac885d1 {n g owner : ℕ} {r : Record} {l : Label} :
    l ∈ row n g owner r ↔
      r.flag=1 ∧ l.owner=owner ∧ start g r.a ≤ l.position ∧ l.position < stop n g r.a := by sorry
