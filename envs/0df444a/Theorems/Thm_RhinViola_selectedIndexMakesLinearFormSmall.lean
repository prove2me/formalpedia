-- Prove2me | Theorems.Thm_RhinViola_selectedIndexMakesLinearFormSmall
-- name    : RhinViola.selectedIndexMakesLinearFormSmall
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:13:37.324245+00:00
-- url     : https://prove2.me/theorems/049cf639-d0be-4d01-ac0f-20f61f2c290e
-- title:
--   Selected exponential index makes the Rhin–Viola linear form small
-- statement:
--   Let u>0 and q>0. If n is at least log(2q)/u and the linear form satisfies |f|≤exp(-un), then q|f|≤1/2. This is the quantitative consequence of the ceiling-index choice in Rhin and Viola's Lemma 4.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem RhinViola.selectedIndexMakesLinearFormSmall
    (u f : ℝ) (q n : ℕ)
    (hu : 0 < u) (hq : 0 < q)
    (hn : Real.log (2 * (q : ℝ)) / u ≤ (n : ℝ))
    (hf : |f| ≤ Real.exp (-(u * (n : ℝ)))) :
    (q : ℝ) * |f| ≤ (1 : ℝ) / 2 := by sorry
