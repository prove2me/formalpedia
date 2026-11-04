-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_mem_allProducts_w3sum_ac885d1
-- name    : ThreeSum.BandRawA.mem_allProducts_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:02.312691+00:00
-- url     : https://prove2.me/theorems/0f313d4c-754d-4ec0-b719-cf7b6b06e217
-- title:
--   Band Raw A: mem all Products
-- statement:
--   The Band Raw A construction uses the mem all Products property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L96-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L96-L112

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.mem_allProducts_w3sum_ac885d1 {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ} :
    t ∈ allProducts nA nB nC g rs ↔
      t.1 < (items nA g rs).length ∧
        t.2.1 ∈ bandPositions nB g (ownerRecord nA g rs t.1).b ∧
        t.2.2 ∈ bandPositions nC g (ownerRecord nA g rs t.1).c := by sorry
