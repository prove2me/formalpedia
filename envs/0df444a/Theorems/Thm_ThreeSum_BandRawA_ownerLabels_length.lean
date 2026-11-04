-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_ownerLabels_length
-- name    : ThreeSum.BandRawA.ownerLabels_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:34.723368+00:00
-- url     : https://prove2.me/theorems/f0cd5589-234e-49b7-ae0a-df1dea2a609d
-- title:
--   Band Raw A: owner Labels length
-- statement:
--   The Band Raw A construction uses the owner Labels length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L95-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L95-L95

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.ownerLabels_length (ls : List Label) : (ownerLabels ls).length=ls.length := by sorry
