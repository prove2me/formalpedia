-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondLow
-- name    : StableVotingDistortion.Lemma9Reduction.secondLow
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:20:30.585266+00:00
-- url     : https://prove2.me/theorems/d0aa7171-9ef2-4e03-b459-69d8031ca553
-- title:
--   Second LP residual at low rank
-- statement:
--   The second low-rank residual is nonpositive for masses from 0.06 through lambda, with the base candidate rank at or above the mass.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperBox PaperMiddle PaperCurve
theorem secondLow {p x : ℝ} (hp : p ∈ Icc pA PaperCurve.lam) (hx : x ∈ Icc p PaperCurve.lam) : p-entry PaperMiddle.Knot.beta p*J score p+max (x-PaperCurve.lam+entry PaperMiddle.Knot.eta p*score x) 0≤0 := by sorry
end StableVotingDistortion.Lemma9Reduction
