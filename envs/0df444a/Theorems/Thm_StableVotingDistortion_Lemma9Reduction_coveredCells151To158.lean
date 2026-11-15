-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells151To158
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells151To158
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:41:17.682581+00:00
-- url     : https://prove2.me/theorems/b6c29421-e467-4104-b361-22c0922b5e02
-- title:
--   Physical residual on mass intervals 151 through 158
-- statement:
--   For each consecutive pair of published knots between masses 363/1000 and 375/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 253 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells151To158 : ∀ cd ∈ ((adjacentCells.drop 151).take 8), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
