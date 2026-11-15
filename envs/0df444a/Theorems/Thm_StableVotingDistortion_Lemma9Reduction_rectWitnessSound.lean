-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_rectWitnessSound
-- name    : StableVotingDistortion.Lemma9Reduction.rectWitnessSound
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T18:19:40.875894+00:00
-- url     : https://prove2.me/theorems/1dea7b2b-e673-4b67-8a3e-a1b626cf8e3d
-- title:
--   Soundness of interval certification for an adjacent mass interval
-- statement:
--   An exact rational partition accepted by the interval checker proves the real-variable physical residual bound on the entire adjacent mass interval. The reduction uses monotonicity and the fundamental theorem of calculus for the published score.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperBox PaperMiddle PaperCurve
theorem rectWitnessSound {k l : PaperMiddle.Knot} (ho : k.position < l.position) (hm : (k,l) ∈ adjacentCells)
    (ok : RectWitness k l (qRank k) (qRank l) 0 (min (qRank l) PaperCurve.lamQ)
      (max (qRank k) PaperCurve.lamQ) 1) : CellCovered k l := by sorry
end StableVotingDistortion.Lemma9Reduction
