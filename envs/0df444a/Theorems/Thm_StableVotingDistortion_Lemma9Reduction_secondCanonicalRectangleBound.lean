-- Prove2me | Theorems.Thm_StableVotingDistortion_Lemma9Reduction_secondCanonicalRectangleBound
-- name    : StableVotingDistortion.Lemma9Reduction.secondCanonicalRectangleBound
-- status  : Proved
-- author  : @a142857a
-- created : 2026-11-14T19:00:37.393466+00:00
-- url     : https://prove2.me/theorems/f3aa5825-1018-4717-85e6-011fa31081cd
-- title:
--   Second canonical residual on a certified three-dimensional rectangle
-- statement:
--   The centered rational test for the released score bounds the second canonical residual throughout its mass and two rank intervals.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic

namespace StableVotingDistortion.Lemma9Reduction
open Set PaperCurve PaperMiddle PaperBox PaperBox.Bounds
theorem secondCanonicalRectangleBound {b c d D : Bounds}
    (hd : D = (let i := clampBox d
    let localBound (r : Piece) : Bounds :=
      let dx := (⟨max i.lo r.lo,min i.hi r.hi⟩ : Bounds).minus (point r.lo)
      r.slopeCoeffs.foldr (fun a acc => (point a).plus (dx.times acc)) (point 0)
    let acc (row : Piece) (rest : Option Bounds) : Option Bounds :=
      if i.lo ≤ row.hi ∧ row.lo ≤ i.hi then
        match rest with
        | none => some (localBound row)
        | some t => some ⟨min (localBound row).lo t.lo,max (localBound row).hi t.hi⟩
      else rest
    ((pieces.foldr acc none).getD (point 0)).times (clampSlopeBox d)))
    (hb : (let x := (d.minus b).plus c
    let e : ℚ := 1+1/20000
    let a := ((c.plus d).plus (quickTotalScoreBox d)).minus (point lamQ)
    let k := ((quickTotalPrimitiveBox x).minus (quickTotalPrimitiveBox d)).minus (quickTotalPrimitiveBox c)
    let s := ((a.times (quickTotalPrimitiveSlope b)).plus ((point e).times k)).minus (((point e).times b).times (quickTotalPrimitiveSlope x))
    let t := (quickTotalPrimitiveBox b).plus (((point e).times b).times ((quickTotalPrimitiveSlope x).minus (quickTotalPrimitiveSlope c)))
    let v := ((quickTotalPrimitiveBox b).times ((point 1).plus D)).plus (((point e).times b).times ((quickTotalPrimitiveSlope x).minus (quickTotalPrimitiveSlope d)))
    let m := anchor b s
    let j := anchor c t
    let y := anchor d v
    let residual := (j+y+quickTotalScore y-lamQ)*quickTotalJ m+e*m*(quickTotalJ (y-m+j)-quickTotalJ y-quickTotalJ j)
    decide (d.hi<b.lo ∨ (d.hi=1 ∧ 0 ≤ v.lo) ∨ residual+deviation b s+deviation c t+deviation d v≤0))=true) {p q z : ℝ}
    (hp : p∈Icc (16/25:ℝ) (99/100)) (hq : q∈Icc (0:ℝ) PaperCurve.lam) (hz : z∈Icc p 1)
    (hbp : (b.lo:ℝ)≤p ∧ p≤b.hi) (hcq : (c.lo:ℝ)≤q ∧ q≤c.hi) (hdz : (d.lo:ℝ)≤z ∧ z≤d.hi) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by sorry
end StableVotingDistortion.Lemma9Reduction
