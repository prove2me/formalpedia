-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_three_lifts_bound
-- name    : ThreeSum.BandRawA.three_lifts_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:57.496238+00:00
-- url     : https://prove2.me/theorems/d302a28a-ccc2-4e53-a2ab-e51ac5f7c894
-- title:
--   Band Raw A: three lifts bound
-- statement:
--   The Band Raw A construction uses the three lifts bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L176-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L176-L180

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.three_lifts_bound {A B C : Family} {n g m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    3*(items n g (records A B C)).length ≤ 9*m^2*g := by sorry
