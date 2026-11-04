-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteBandEquiv_value
-- name    : ThreeSum.BandRawA.finiteBandEquiv_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:29.397378+00:00
-- url     : https://prove2.me/theorems/018a9419-3d80-4680-a4a3-94514ad1c5c3
-- title:
--   Band Raw A: finite Band Equiv value
-- statement:
--   The Band Raw A construction uses the finite Band Equiv value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L46-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L46-L47

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.finiteBandEquiv_value (n g a : ℕ) (f : ℕ → ℤ) (j : Fin (bandLength n g a)) :
    f (finiteBandEquiv n g a j).val.val=f (BandPartition.start g a+j.val) := by sorry
