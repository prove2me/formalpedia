-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalFirstLowerRanks
-- name    : StableVotingDistortion.Lemma9Reduction.canonicalFirstLowerRanks
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:28:29.657761+00:00
-- url     : https://prove2.me/theorems/48a3fd10-f79b-44fd-ab25-544bd71aa657
-- title:
--   First canonical residual on the lower half of the rank interval
-- statement:
--   For every mass between 16/25 and 99/100, the published first canonical inequality holds for all ranks in the closed interval [0, 703/2500]. Its release certificate covers this range with 486 rational rectangles.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperBox PaperMiddle PaperCurve
theorem canonicalFirstLowerRanks {p q : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (0:ℝ) ((703/2500):ℝ)) : q+PaperMiddle.canonical score p*deltaP score p q ≤ PaperCurve.lam := by sorry
end StableVotingDistortion.Lemma9Reduction
