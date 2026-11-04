-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_bandLength_eq_min
-- name    : ThreeSum.BandRawA.bandLength_eq_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:26:53.33569+00:00
-- url     : https://prove2.me/theorems/0ce02f38-a159-4388-a090-dc1c3e7aba49
-- title:
--   Band Raw A: band Length eq min
-- statement:
--   The Band Raw A construction uses the band Length eq min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L26-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L26-L29

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.bandLength_eq_min (n g a : ℕ) : bandLength n g a=min g (n-start g a) := by sorry
