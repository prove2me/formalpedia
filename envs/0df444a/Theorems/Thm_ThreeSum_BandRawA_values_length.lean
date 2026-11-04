-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_values_length
-- name    : ThreeSum.BandRawA.values_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:13.890748+00:00
-- url     : https://prove2.me/theorems/fbbd1b87-f50c-42fa-bd93-a7bf7754ad2f
-- title:
--   Band Raw A: values length
-- statement:
--   The Band Raw A construction uses the values length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L94-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L94-L94

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
import Theorems.Thm_ThreeSum_RadixKeyLists_values_length

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.values_length (f : ℕ → ℤ) (ls : List Label) : (values f ls).length=ls.length := by sorry
