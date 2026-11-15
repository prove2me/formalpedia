-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_firstLowCorrectionBudget
-- name    : StableVotingDistortion.Lemma9Reduction.firstLowCorrectionBudget
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:32:08.245625+00:00
-- url     : https://prove2.me/theorems/6281b75e-cedc-4344-a7e6-e1624579423f
-- title:
--   First low-rank bound at zero offset
-- statement:
--   For each released LP mass from 0.06 to 0.64 and each rank from zero to lambda, the zero-offset primitive term and the positive-part correction sum to at most lambda.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperMiddle PaperCurve PaperBox
theorem firstLowCorrectionBudget {p x : ℝ} (hp : p ∈ Icc (3/50:ℝ) (16/25)) (hx : x ∈ Icc (0:ℝ) PaperCurve.lam) :
    entry PaperMiddle.Knot.beta p * J score (1-p) +
      max (entry PaperMiddle.Knot.eta p * score x + x - PaperCurve.lam) 0 ≤ PaperCurve.lam := by sorry
end StableVotingDistortion.Lemma9Reduction
