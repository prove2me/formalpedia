-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_ownerProduct_bounds
-- name    : ThreeSum.BandRawA.ownerProduct_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:30.285794+00:00
-- url     : https://prove2.me/theorems/6549833d-9952-4ebb-b6be-aa8c90f0fb03
-- title:
--   Band Raw A: owner Product bounds
-- statement:
--   The Band Raw A construction uses the owner Product bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L72-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L72-L76

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.ownerProduct_bounds {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) (ht : t ∈ ownerProduct nA nB nC g rs s) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by sorry
