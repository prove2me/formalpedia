-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells136To142
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells136To142
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:41:17.187293+00:00
-- url     : https://prove2.me/theorems/a904397a-bef5-457c-91ac-37e4e993b09b
-- title:
--   Physical residual on mass intervals 136 through 142
-- statement:
--   For each consecutive pair of published knots between masses 348/1000 and 355/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 254 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells136To142 : ∀ cd ∈ ((adjacentCells.drop 136).take 7), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
