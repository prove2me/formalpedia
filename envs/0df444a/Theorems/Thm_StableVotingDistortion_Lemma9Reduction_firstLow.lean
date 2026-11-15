-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_firstLow
-- name    : StableVotingDistortion.Lemma9Reduction.firstLow
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:08:34.65474+00:00
-- url     : https://prove2.me/theorems/4e160dc8-6f0f-48cb-a1d4-83e77b309fd0
-- title:
--   First LP residual over the full low interval
-- statement:
--   For masses from 0.06 through 0.64, the first low-rank residual is nonpositive for every admissible attack rank, using the published affine coefficient table.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperBox PaperMiddle PaperCurve
theorem firstLow {p q x : ℝ} (hp : p ∈ Icc (3/50:ℝ) (16/25)) (hq : q ∈ Icc (0:ℝ) p) (hx : x ∈ Icc (0:ℝ) PaperCurve.lam) : lowFirst PaperCurve.lam score (entry PaperMiddle.Knot.beta p) (-1) (entry PaperMiddle.Knot.eta p) p q x ≤ 0 := by sorry
end StableVotingDistortion.Lemma9Reduction
