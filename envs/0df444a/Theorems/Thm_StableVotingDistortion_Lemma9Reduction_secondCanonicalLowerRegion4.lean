-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalLowerRegion4
-- name    : StableVotingDistortion.Lemma9Reduction.secondCanonicalLowerRegion4
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T19:08:27.151207+00:00
-- url     : https://prove2.me/theorems/38a33f1c-55ad-4a08-940c-6cf71b0022ae
-- title:
--   Second canonical residual on lower rank region 4
-- statement:
--   The released second canonical residual is nonpositive for all feasible masses and ranks on the closed region (('16/25', '163/200'), ('703/5000', '703/2500'), ('91/100', '1')). The certificate checks 52 exact rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
theorem secondCanonicalLowerRegion4 {p q z : ℝ} (hp : p∈Icc (16/25:ℝ) (99/100)) (hq : q∈Icc (0:ℝ) PaperCurve.lam) (hz : z∈Icc p 1) (bp : p∈Icc ((16/25):ℝ) ((163/200):ℝ)) (bq : q∈Icc ((703/5000):ℝ) ((703/2500):ℝ)) (bz : z∈Icc ((91/100):ℝ) (1:ℝ)) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by sorry
end StableVotingDistortion.Lemma9Reduction
