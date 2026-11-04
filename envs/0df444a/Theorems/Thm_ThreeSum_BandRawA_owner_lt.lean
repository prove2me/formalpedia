-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_owner_lt
-- name    : ThreeSum.BandRawA.owner_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:05:01.436653+00:00
-- url     : https://prove2.me/theorems/3a621c9e-97e3-438d-a8d6-03267083dc2e
-- title:
--   Band Raw A: owner lt
-- statement:
--   The Band Raw A construction uses the owner lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L140-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L140-L141

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.owner_lt {n g : ℕ} {rs : List Record} {l : Label}
    (hl : l ∈ items n g rs) : l.owner < rs.length := by sorry
