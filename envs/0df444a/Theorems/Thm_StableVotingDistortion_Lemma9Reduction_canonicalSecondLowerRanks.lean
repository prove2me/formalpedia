-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalSecondLowerRanks
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalSecondLowerRanks
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:48:22.902964+00:00
-- url     : https://prove2.me/theorems/c9f58e84-d067-422e-bdc5-1e3d35a44127
-- title:
--   Second canonical residual on the lower half of the rank interval
-- statement:
--   For each mass from 16/25 to 99/100 and terminal rank from the mass to one, the published second canonical residual is nonpositive when the initial rank lies in [0, 703/2500].
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperBox PaperMiddle PaperCurve
theorem canonicalSecondLowerRanks {p q z : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (0:ℝ) (703/2500:ℝ)) (hz : z ∈ Icc p 1) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by sorry
end StableVotingDistortion.Lemma9Reduction
