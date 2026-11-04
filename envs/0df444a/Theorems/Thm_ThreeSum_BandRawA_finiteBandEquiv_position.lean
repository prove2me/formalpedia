-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteBandEquiv_position
-- name    : ThreeSum.BandRawA.finiteBandEquiv_position
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:47.202198+00:00
-- url     : https://prove2.me/theorems/678e2130-4823-4a5f-aa07-25ed3bec3ea8
-- title:
--   Band Raw A: finite Band Equiv position
-- statement:
--   The Band Raw A construction uses the finite Band Equiv position property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L43-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L43-L44

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.finiteBandEquiv_position (n g a : ℕ) (j : Fin (bandLength n g a)) :
    (finiteBandEquiv n g a j).val.val=BandPartition.start g a+j.val := by sorry
