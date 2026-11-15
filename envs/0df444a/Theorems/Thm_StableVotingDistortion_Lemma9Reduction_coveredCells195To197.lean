-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells195To197
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells195To197
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:44:23.161471+00:00
-- url     : https://prove2.me/theorems/7657a8d4-e58e-4143-831b-56c8e0a9c423
-- title:
--   Physical residual on mass intervals 195 through 197
-- statement:
--   For each consecutive pair of published knots between masses 555/1000 and 570/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 236 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells195To197 : ∀ cd ∈ ((adjacentCells.drop 195).take 3), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
