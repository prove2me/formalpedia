-- Prove2me | Theorems.Thm_RhinViola_selectedIndexErrorLowerBound
-- name    : RhinViola.selectedIndexErrorLowerBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T20:36:23.008976+00:00
-- url     : https://prove2.me/theorems/702f4197-6bce-4241-b6f1-cc5c1b325426
-- title:
--   Selected-index exponential lower bound for the Rhin–Viola approximation error
-- statement:
--   At the index n chosen large enough that q|f|≤1/2, suppose exp(-vn)≤|f| and |b|≤exp(wn). The uniform scaled determinant bound then implies exp(-(v+w)n)≤|α-p/q| for every integer numerator p. This combines the zero- and nonzero-determinant branches into one source-faithful exponential error bound.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Theorems.Thm_RhinViola_integerLinearFormScaledLowerBound
import Theorems.Thm_RhinViola_selectedIndexMakesLinearFormSmall
import Mathlib.Tactic

theorem RhinViola.selectedIndexErrorLowerBound
    (α f u v w : ℝ) (a b p : ℤ) (q n : ℕ)
    (hq : 0 < q) (hb : b ≠ 0) (hu : 0 < u)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hn : Real.log (2 * (q : ℝ)) / u ≤ (n : ℝ))
    (hf_upper : |f| ≤ Real.exp (-(u * (n : ℝ))))
    (hf_lower : Real.exp (-(v * (n : ℝ))) ≤ |f|)
    (hb_upper : |(b : ℝ)| ≤ Real.exp (w * (n : ℝ))) :
    Real.exp (-((v + w) * (n : ℝ))) ≤
      |α - (p : ℝ) / (q : ℝ)| := by sorry
