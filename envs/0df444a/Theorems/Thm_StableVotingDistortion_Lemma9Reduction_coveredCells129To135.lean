-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells129To135
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells129To135
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:39:04.973589+00:00
-- url     : https://prove2.me/theorems/adab8956-625e-4e31-9938-7c3836a75c42
-- title:
--   Physical residual on mass intervals 129 through 135
-- statement:
--   For each consecutive pair of published knots between masses 341/1000 and 348/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 261 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells129To135 : ∀ cd ∈ ((adjacentCells.drop 129).take 7), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
