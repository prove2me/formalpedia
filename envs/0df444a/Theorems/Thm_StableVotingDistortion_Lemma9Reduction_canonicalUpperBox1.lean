-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox1
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalUpperBox1
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:54:53.095182+00:00
-- url     : https://prove2.me/theorems/f25d9be1-4372-47f3-b6ab-6016273b8e9c
-- title:
--   First canonical residual on mass and rank rectangle upper 1
-- statement:
--   The canonical first residual is bounded throughout the closed mass interval [16/25,163/200] and rank interval [703/2500,703/1250]. This part of the certificate contains 12 rectangles.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
theorem canonicalUpperBox1 {p q : ℝ} (hp : p∈Icc ((16/25):ℝ) ((163/200):ℝ)) (hq : q∈Icc ((703/2500):ℝ) ((703/1250):ℝ)) : q+PaperMiddle.canonical PaperCurve.score p*deltaP PaperCurve.score p q ≤ PaperCurve.lam := by sorry
end StableVotingDistortion.Lemma9Reduction
