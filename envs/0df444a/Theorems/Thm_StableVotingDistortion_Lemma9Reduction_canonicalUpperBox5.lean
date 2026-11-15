-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox5
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalUpperBox5
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:54:57.600946+00:00
-- url     : https://prove2.me/theorems/879d4f2e-1759-496a-aa7d-cfd36c740bb8
-- title:
--   First canonical residual on mass and rank rectangle upper 5
-- statement:
--   The canonical first residual is bounded throughout the closed mass interval [163/200,99/100] and rank interval [2109/5000,703/1250]. This part of the certificate contains 145 rectangles.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
theorem canonicalUpperBox5 {p q : ℝ} (hp : p∈Icc ((163/200):ℝ) ((99/100):ℝ)) (hq : q∈Icc ((2109/5000):ℝ) ((703/1250):ℝ)) : q+PaperMiddle.canonical PaperCurve.score p*deltaP PaperCurve.score p q ≤ PaperCurve.lam := by sorry
end StableVotingDistortion.Lemma9Reduction
