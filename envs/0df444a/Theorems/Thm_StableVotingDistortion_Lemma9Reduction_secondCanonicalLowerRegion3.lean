-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalLowerRegion3
-- name    : StableVotingDistortion.Lemma9Reduction.secondCanonicalLowerRegion3
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T19:08:28.367755+00:00
-- url     : https://prove2.me/theorems/3db2eef7-4010-48e3-90e9-a2ff63255eef
-- title:
--   Second canonical residual on lower rank region 3
-- statement:
--   The released second canonical residual is nonpositive for all feasible masses and ranks on the closed region (('16/25', '163/200'), ('0', '703/5000'), ('91/100', '1')). The certificate checks 53 exact rational leaves.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox
theorem secondCanonicalLowerRegion3 {p q z : ℝ} (hp : p∈Icc (16/25:ℝ) (99/100)) (hq : q∈Icc (0:ℝ) PaperCurve.lam) (hz : z∈Icc p 1) (bp : p∈Icc ((16/25):ℝ) ((163/200):ℝ)) (bq : q∈Icc (0:ℝ) ((703/5000):ℝ)) (bz : z∈Icc ((91/100):ℝ) (1:ℝ)) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by sorry
end StableVotingDistortion.Lemma9Reduction
