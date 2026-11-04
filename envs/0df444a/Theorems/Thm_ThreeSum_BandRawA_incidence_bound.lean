-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_incidence_bound
-- name    : ThreeSum.BandRawA.incidence_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:27:06.893332+00:00
-- url     : https://prove2.me/theorems/4c4e9bc6-3bbe-4ff7-aa3b-0f475d9e73dd
-- title:
--   Band Raw A: incidence bound
-- statement:
--   The Band Raw A construction uses the incidence bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L169-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawA.lean#L169-L174

import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_BandRawA
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows BandEnumeration BandPartition
set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.incidence_bound {A B C : Family} {n g m : ℕ}
    (hA : A.size ≤ m) (hB : B.size ≤ m) (hC : C.size ≤ m) :
    (items n g (records A B C)).length ≤ 3*m^2*g := by sorry
