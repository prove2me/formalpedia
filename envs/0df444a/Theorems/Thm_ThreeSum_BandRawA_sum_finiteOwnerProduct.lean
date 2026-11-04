-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_sum_finiteOwnerProduct
-- name    : ThreeSum.BandRawA.sum_finiteOwnerProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:33.363726+00:00
-- url     : https://prove2.me/theorems/6be5cc8f-46ff-40e1-bd98-8d2124c90a06
-- title:
--   Band Raw A: sum finite Owner Product
-- statement:
--   The Band Raw A construction uses the sum finite Owner Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L98-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L98-L111

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.sum_finiteOwnerProduct (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) {s : ℕ} (hs : s < rs.length) :
    (∑ u ∈ finiteOwnerProduct nA nB nC g rs s, F (coordinates u))=
      ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by sorry
