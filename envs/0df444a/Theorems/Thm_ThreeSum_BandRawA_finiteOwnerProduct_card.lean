-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_finiteOwnerProduct_card
-- name    : ThreeSum.BandRawA.finiteOwnerProduct_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:07.671036+00:00
-- url     : https://prove2.me/theorems/1f3ac00b-ec99-4c3d-b4a3-5691f5a7b850
-- title:
--   Band Raw A: finite Owner Product card
-- statement:
--   The Band Raw A construction uses the finite Owner Product card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L97-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFiniteSlices.lean#L97-L103

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem ThreeSum.BandRawA.finiteOwnerProduct_card (nA nB nC g : ℕ) (rs : List Record) (s : ℕ)
    (hs : s < rs.length) :
    (finiteOwnerProduct nA nB nC g rs s).card=
      (row nA g s (rs.getD s default)).length*
        bandLength nB g (rs.getD s default).b*bandLength nC g (rs.getD s default).c := by sorry
