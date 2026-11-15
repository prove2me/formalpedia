-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells000To020
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells000To020
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:37:17.550962+00:00
-- url     : https://prove2.me/theorems/2d5ee249-6d03-48e1-9ffc-9bf253f4e249
-- title:
--   Physical residual on mass intervals 0 through 20
-- statement:
--   For each consecutive pair of published knots between masses 60/1000 and 165/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 276 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells000To020 : ∀ cd ∈ ((adjacentCells.drop 0).take 21), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
