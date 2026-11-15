-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalFirst
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalFirst
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:19:09.803982+00:00
-- url     : https://prove2.me/theorems/9cb4d632-d570-40e3-b6c7-0d7fb0f6d7f6
-- title:
--   First residual for canonical mass coefficients
-- statement:
--   For masses from 0.64 through 0.99 and attack rank at most lambda, the canonical coefficient satisfies the first verified inequality.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperBox PaperMiddle PaperCurve
theorem canonicalFirst {p q : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (0:ℝ) PaperCurve.lam) : q+PaperMiddle.canonical score p*deltaP score p q ≤ PaperCurve.lam := by sorry
end StableVotingDistortion.Lemma9Reduction
