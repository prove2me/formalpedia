-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_ownerProduct_disjoint
-- name    : ThreeSum.BandRawA.ownerProduct_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:46.236398+00:00
-- url     : https://prove2.me/theorems/fb5d983d-6ff6-44c5-8a32-1eab1484b937
-- title:
--   Band Raw A: owner Product disjoint
-- statement:
--   The Band Raw A construction uses the owner Product disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L87-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L87-L94

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (ownerProduct nA nB nC g rs s) (ownerProduct nA nB nC g rs t) := by sorry
