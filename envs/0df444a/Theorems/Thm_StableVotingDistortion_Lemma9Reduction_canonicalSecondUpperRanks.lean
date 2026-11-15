-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalSecondUpperRanks
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalSecondUpperRanks
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:48:25.709238+00:00
-- url     : https://prove2.me/theorems/a2c10eaa-5990-4181-85dd-8f402db9a95e
-- title:
--   Second canonical residual on the upper half of the rank interval
-- statement:
--   For each mass from 16/25 to 99/100 and terminal rank from the mass to one, the published second canonical residual is nonpositive when the initial rank lies in [703/2500, 703/1250].
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperBox PaperMiddle PaperCurve
theorem canonicalSecondUpperRanks {p q z : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (703/2500:ℝ) PaperCurve.lam) (hz : z ∈ Icc p 1) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by sorry
end StableVotingDistortion.Lemma9Reduction
