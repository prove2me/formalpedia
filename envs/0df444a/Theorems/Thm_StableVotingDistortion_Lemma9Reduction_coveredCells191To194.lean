-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells191To194
-- name    : StableVotingDistortion.Lemma9Reduction.coveredCells191To194
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:42:55.327406+00:00
-- url     : https://prove2.me/theorems/798b6f97-5d10-4818-a19f-7dbeda051392
-- title:
--   Physical residual on mass intervals 191 through 194
-- statement:
--   For each consecutive pair of published knots between masses 535/1000 and 555/1000, the Section 6 physical LP residual is nonpositive throughout the admissible rectangle. The certificate verifies 274 rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open PaperMiddle
theorem coveredCells191To194 : ∀ cd ∈ ((adjacentCells.drop 191).take 4), CellCovered cd.1 cd.2 := by sorry
end StableVotingDistortion.Lemma9Reduction
