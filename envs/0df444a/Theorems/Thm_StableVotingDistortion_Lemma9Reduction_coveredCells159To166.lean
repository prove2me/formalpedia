-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells159To166
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells159To166
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:41:27.016284+00:00
-- url     : https://prove2.me/theorems/67a00dbf-6f4a-49a8-932e-91153155451f
-- title:
--   Physical residual on mass intervals 159 through 166
-- statement:
--   For each consecutive pair of published knots between masses 375/1000 and 415/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 268 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells159To166 : ∀ cd ∈ ((adjacentCells.drop 159).take 8), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
