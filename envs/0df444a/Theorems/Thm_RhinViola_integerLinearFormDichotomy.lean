-- Prove2me | Theorems.Thm_RhinViola_integerLinearFormDichotomy
-- name    : RhinViola.integerLinearFormDichotomy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:26:47.661656+00:00
-- url     : https://prove2.me/theorems/0dee7ba5-7db8-4a1a-a8f3-5b678c59af1f
-- title:
--   Determinant dichotomy for the Rhin–Viola integer linear-form argument
-- statement:
--   For a nonzero integer coefficient b and positive denominator q, if the linear form f=a−bα is small enough that q|f|≤1/2, then the integer determinant qa−pb either vanishes, giving the exact identity |α−p/q|=|f|/|b|, or is nonzero, giving the separation inequality 1/2≤|b|q|α−p/q|. This packages the two arithmetic branches of Rhin and Viola's Lemma 4.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Theorems.Thm_RhinViola_nonzeroDeterminantSeparation
import Theorems.Thm_RhinViola_zeroDeterminantIdentity

theorem RhinViola.integerLinearFormDichotomy
    (α f : ℝ) (a b p : ℤ) (q : ℕ)
    (hq : 0 < q) (hb : b ≠ 0)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hsmall : (q : ℝ) * |f| ≤ (1 : ℝ) / 2) :
    |α - (p : ℝ) / (q : ℝ)| = |f| / |(b : ℝ)| ∨
      (1 : ℝ) / 2 ≤ |(b : ℝ)| * (q : ℝ) *
        |α - (p : ℝ) / (q : ℝ)| := by sorry
