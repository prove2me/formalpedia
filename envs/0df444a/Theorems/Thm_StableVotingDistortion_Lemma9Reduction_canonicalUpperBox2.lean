-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox2
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalUpperBox2
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:54:52.499243+00:00
-- url     : https://prove2.me/theorems/d398e7ee-fe17-4d2d-9807-599c5c4ce3a8
-- title:
--   First canonical residual on mass and rank rectangle upper 2
-- statement:
--   The canonical first residual is bounded throughout the closed mass interval [163/200,361/400] and rank interval [703/2500,2109/5000]. This part of the certificate contains 68 rectangles.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
theorem canonicalUpperBox2 {p q : ℝ} (hp : p∈Icc ((163/200):ℝ) ((361/400):ℝ)) (hq : q∈Icc ((703/2500):ℝ) ((2109/5000):ℝ)) : q+PaperMiddle.canonical PaperCurve.score p*deltaP PaperCurve.score p q ≤ PaperCurve.lam := by sorry
end StableVotingDistortion.Lemma9Reduction
