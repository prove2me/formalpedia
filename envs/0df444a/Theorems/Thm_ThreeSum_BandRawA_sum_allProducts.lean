-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_sum_allProducts
-- name    : ThreeSum.BandRawA.sum_allProducts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:34.961932+00:00
-- url     : https://prove2.me/theorems/0a123ceb-f75d-4b9a-be65-222f69eede4f
-- title:
--   Band Raw A: sum all Products
-- statement:
--   The Band Raw A construction uses the sum all Products property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L143-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L143-L150

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ t ∈ allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by sorry
