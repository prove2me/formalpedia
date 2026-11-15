-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalLowerRegion5
-- name    : StableVotingDistortion.Lemma9Reduction.secondCanonicalLowerRegion5
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T19:08:27.31398+00:00
-- url     : https://prove2.me/theorems/97a489be-15f2-4c66-8cc4-0a8343d79137
-- title:
--   Second canonical residual on lower rank region 5
-- statement:
--   The released second canonical residual is nonpositive for all feasible masses and ranks on the closed region (('163/200', '99/100'), ('0', '703/2500'), ('41/50', '1')). The certificate checks 12 exact rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
theorem secondCanonicalLowerRegion5 {p q z : ℝ} (hp : p∈Icc (16/25:ℝ) (99/100)) (hq : q∈Icc (0:ℝ) PaperCurve.lam) (hz : z∈Icc p 1) (bp : p∈Icc ((163/200):ℝ) ((99/100):ℝ)) (bq : q∈Icc (0:ℝ) ((703/2500):ℝ)) (bz : z∈Icc ((41/50):ℝ) (1:ℝ)) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by sorry
end StableVotingDistortion.Lemma9Reduction
