-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_sum_finiteAllProducts
-- name    : ThreeSum.BandRawA.sum_finiteAllProducts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:04.943196+00:00
-- url     : https://prove2.me/theorems/813d115f-265d-4052-b352-406c2658aa8b
-- title:
--   Band Raw A: sum finite All Products
-- statement:
--   The Band Raw A construction uses the sum finite All Products property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L113-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAFinite.lean#L113-L126

import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Definitions.Def_Submission_ThreeSum_BandRawAFinite
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ u ∈ finiteAllProducts nA nB nC g rs, F (coordinates u))=
      ∑ t ∈ allProducts nA nB nC g rs, F t := by sorry
