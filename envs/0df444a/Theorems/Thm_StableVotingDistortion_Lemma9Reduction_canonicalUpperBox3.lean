-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalUpperBox3
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalUpperBox3
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:54:58.798194+00:00
-- url     : https://prove2.me/theorems/ef01de82-a15d-4f54-a590-5520303f2c69
-- title:
--   First canonical residual on mass and rank rectangle upper 3
-- statement:
--   The canonical first residual is bounded throughout the closed mass interval [361/400,99/100] and rank interval [703/2500,703/2000]. This part of the certificate contains 287 rectangles.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
theorem canonicalUpperBox3 {p q : ℝ} (hp : p∈Icc ((361/400):ℝ) ((99/100):ℝ)) (hq : q∈Icc ((703/2500):ℝ) ((703/2000):ℝ)) : q+PaperMiddle.canonical PaperCurve.score p*deltaP PaperCurve.score p q ≤ PaperCurve.lam := by sorry
end StableVotingDistortion.Lemma9Reduction
