-- Prove2me | Theorems.Thm_RhinViola_integerLinearFormScaledLowerBound
-- name    : RhinViola.integerLinearFormScaledLowerBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T18:31:02.97501+00:00
-- url     : https://prove2.me/theorems/85cc8d6f-d319-4963-8b66-fcd0ab6852a2
-- title:
--   Uniform scaled lower bound from the Rhin–Viola determinant dichotomy
-- statement:
--   Suppose f=a-bα is an integer linear form, b is nonzero, q is positive and q|f|≤1/2. If L is any lower bound for |f| and U is any upper bound for |b|, then the determinant dichotomy implies min(qL,1/2)≤Uq|α-p/q| uniformly in the integer numerator p. This packages both branches into the multiplicative inequality needed by the exponential-rate part of Rhin and Viola's Lemma 4.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Theorems.Thm_RhinViola_integerLinearFormDichotomy
import Mathlib.Tactic

theorem RhinViola.integerLinearFormScaledLowerBound
    (α f L U : ℝ) (a b p : ℤ) (q : ℕ)
    (hq : 0 < q) (hb : b ≠ 0)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hsmall : (q : ℝ) * |f| ≤ (1 : ℝ) / 2)
    (hL : L ≤ |f|) (hU : |(b : ℝ)| ≤ U) :
    min ((q : ℝ) * L) ((1 : ℝ) / 2) ≤
      U * (q : ℝ) * |α - (p : ℝ) / (q : ℝ)| := by sorry
