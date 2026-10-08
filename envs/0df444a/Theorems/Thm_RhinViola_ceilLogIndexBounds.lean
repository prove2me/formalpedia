-- Prove2me | Theorems.Thm_RhinViola_ceilLogIndexBounds
-- name    : RhinViola.ceilLogIndexBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:11:32.195303+00:00
-- url     : https://prove2.me/theorems/a1128b7b-5ab6-44f8-9e3a-6f43463ed1a6
-- title:
--   Ceiling index bounds for the Rhin–Viola irrationality criterion
-- statement:
--   For u>0 and a positive natural denominator q, set n to the natural ceiling of log(2q)/u. Then log(2q)/u≤n<log(2q)/u+1. This is the exact integer-index choice used in Rhin and Viola's Lemma 4 to balance the denominator q against exponential decay.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem RhinViola.ceilLogIndexBounds
    (u : ℝ) (q : ℕ) (hu : 0 < u) (hq : 0 < q) :
    let n : ℕ := ⌈Real.log (2 * (q : ℝ)) / u⌉₊
    Real.log (2 * (q : ℝ)) / u ≤ (n : ℝ) ∧
      (n : ℝ) < Real.log (2 * (q : ℝ)) / u + 1 := by sorry
