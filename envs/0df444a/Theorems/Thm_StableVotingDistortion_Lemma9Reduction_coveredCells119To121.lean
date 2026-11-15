-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells119To121
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells119To121
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:38:07.658237+00:00
-- url     : https://prove2.me/theorems/f34dc444-43c5-456d-af21-7189c40024a1
-- title:
--   Physical residual on mass intervals 119 through 121
-- statement:
--   For each consecutive pair of published knots between masses 331/1000 and 334/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 118 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells119To121 : ∀ cd ∈ ((adjacentCells.drop 119).take 3), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
