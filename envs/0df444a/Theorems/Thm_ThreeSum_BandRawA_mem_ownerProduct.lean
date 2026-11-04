-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_ownerProduct
-- name    : ThreeSum.BandRawA.mem_ownerProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:43.49763+00:00
-- url     : https://prove2.me/theorems/f8998085-efc8-4a6d-b0df-0f7e22744aff
-- title:
--   Band Raw A: mem owner Product
-- statement:
--   The Band Raw A construction uses the mem owner Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L79-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L79-L85

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by sorry
