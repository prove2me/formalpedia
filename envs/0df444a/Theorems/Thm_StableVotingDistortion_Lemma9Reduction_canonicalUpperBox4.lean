-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox4
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalUpperBox4
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:54:57.826064+00:00
-- url     : https://prove2.me/theorems/e81b9950-05af-4c32-b5cf-482cd2998861
-- title:
--   First canonical residual on mass and rank rectangle upper 4
-- statement:
--   The canonical first residual is bounded throughout the closed mass interval [361/400,99/100] and rank interval [703/2000,2109/5000]. This part of the certificate contains 226 rectangles.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
theorem canonicalUpperBox4 {p q : ℝ} (hp : p∈Icc ((361/400):ℝ) ((99/100):ℝ)) (hq : q∈Icc ((703/2000):ℝ) ((2109/5000):ℝ)) : q+PaperMiddle.canonical PaperCurve.score p*deltaP PaperCurve.score p q ≤ PaperCurve.lam := by sorry
end StableVotingDistortion.Lemma9Reduction
