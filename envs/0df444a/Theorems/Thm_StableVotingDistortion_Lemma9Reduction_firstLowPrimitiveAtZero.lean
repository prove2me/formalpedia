-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_firstLowPrimitiveAtZero
-- name    : StableVotingDistortion.Lemma9Reduction.firstLowPrimitiveAtZero
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:32:04.823452+00:00
-- url     : https://prove2.me/theorems/110faddf-8767-4c8b-b266-51aa86b6ecb4
-- title:
--   Primitive contribution at zero offset
-- statement:
--   For each released LP mass from 0.06 to 0.64 and offset q between zero and p, the first primitive contribution at q is at most its value at zero.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperMiddle PaperCurve PaperBox
theorem firstLowPrimitiveAtZero {p q : ℝ} (hp : p ∈ Icc (3/50:ℝ) (16/25)) (hq : q ∈ Icc (0:ℝ) p) :
    q + entry PaperMiddle.Knot.beta p * deltaP score p q ≤ entry PaperMiddle.Knot.beta p * J score (1-p) := by sorry
end StableVotingDistortion.Lemma9Reduction
