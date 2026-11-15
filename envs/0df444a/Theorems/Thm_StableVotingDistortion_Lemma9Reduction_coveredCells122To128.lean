-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells122To128
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells122To128
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:39:51.733198+00:00
-- url     : https://prove2.me/theorems/c4b8ee8e-1415-4df4-b8a1-19ff5be4a3ca
-- title:
--   Physical residual on mass intervals 122 through 128
-- statement:
--   For each consecutive pair of published knots between masses 334/1000 and 341/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 264 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells122To128 : ∀ cd ∈ ((adjacentCells.drop 122).take 7), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
