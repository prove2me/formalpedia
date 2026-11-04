-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteAllProducts_eq_union
-- name    : ThreeSum.BandRawA.finiteAllProducts_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:46.027145+00:00
-- url     : https://prove2.me/theorems/290e992f-2c5a-4b1d-a2fc-760a9537c6d4
-- title:
--   Band Raw A: finite All Products eq union
-- statement:
--   The Band Raw A construction uses the finite All Products eq union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L154-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L154-L158

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.finiteAllProducts_eq_union (nA nB nC g : ℕ) (rs : List Record) :
    finiteAllProducts nA nB nC g rs=
      (range rs.length).biUnion (finiteOwnerProduct nA nB nC g rs) := by sorry
