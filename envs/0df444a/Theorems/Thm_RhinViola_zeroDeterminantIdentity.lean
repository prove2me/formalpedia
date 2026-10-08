-- Prove2me | Theorems.Thm_RhinViola_zeroDeterminantIdentity
-- name    : RhinViola.zeroDeterminantIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T07:36:42.229688+00:00
-- url     : https://prove2.me/theorems/e8146b4e-182b-4d10-9c4a-5ce01812e39b
-- title:
--   Zero-determinant identity in the Rhin–Viola irrationality criterion
-- statement:
--   Let f=a-bα. If q is positive, b is nonzero and the integer determinant qa-pb vanishes, then a/b=p/q and hence f=-b(α-p/q). Taking absolute values gives the exact identity |α-p/q|=|f|/|b|. This is the zero-determinant branch of Rhin and Viola's abstract irrationality-measure criterion.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Tactic
import Mathlib.Data.Int.Cast.Lemmas

theorem RhinViola.zeroDeterminantIdentity
    (α f : ℝ) (a b p : ℤ) (q : ℕ)
    (hq : 0 < q) (hb : b ≠ 0)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hdet : (q : ℤ) * a = p * b) :
    |α - (p : ℝ) / (q : ℝ)| = |f| / |(b : ℝ)| := by sorry
