-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteOwnerProduct_disjoint
-- name    : ThreeSum.BandRawA.finiteOwnerProduct_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:43.627991+00:00
-- url     : https://prove2.me/theorems/d6c25d3d-ef4c-4347-98f3-d2bceb867642
-- title:
--   Band Raw A: finite Owner Product disjoint
-- statement:
--   The Band Raw A construction uses the finite Owner Product disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L160-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L160-L166

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.finiteOwnerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hne : s ≠ t) :
    Disjoint (finiteOwnerProduct nA nB nC g rs s) (finiteOwnerProduct nA nB nC g rs t) := by sorry
