-- Prove2me | Theorems.Thm_ThreeSum_BandRawA_sum_ownerProduct
-- name    : ThreeSum.BandRawA.sum_ownerProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:28:04.391081+00:00
-- url     : https://prove2.me/theorems/b11fb7db-518d-4315-baa5-327515240e3d
-- title:
--   Band Raw A: sum owner Product
-- statement:
--   The Band Raw A construction uses the sum owner Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L126-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BandRawAProduct.lean#L126-L141

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

theorem ThreeSum.BandRawA.sum_ownerProduct (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) (s : ℕ) :
    (∑ t ∈ ownerProduct nA nB nC g rs s, F t)=
      ∑ i ∈ range (row nA g s (rs.getD s default)).length,
        ∑ j ∈ range (bandLength nB g (rs.getD s default).b),
          ∑ k ∈ range (bandLength nC g (rs.getD s default).c),
            F (count nA g rs s+i,
              BandPartition.start g (rs.getD s default).b+j,
              BandPartition.start g (rs.getD s default).c+k) := by sorry
