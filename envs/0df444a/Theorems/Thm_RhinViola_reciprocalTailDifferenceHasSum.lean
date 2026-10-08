-- Prove2me | Theorems.Thm_RhinViola_reciprocalTailDifferenceHasSum
-- name    : RhinViola.reciprocalTailDifferenceHasSum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T17:14:11.865292+00:00
-- url     : https://prove2.me/theorems/5e7548f3-b665-4162-a97e-df09a7939acb
-- title:
--   Telescoping reciprocal tail used in the Rhin-Viola off-diagonal kernel
-- statement:
--   For every natural a, the series of consecutive reciprocal differences telescopes: summing 1/(k+a+1)-1/(k+a+2) over k >= 0 gives exactly 1/(a+1). This is the one-step tail identity used to sum the off-diagonal Rhin-Viola monomial kernel.
-- source:
--   Elementary telescoping identity used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

theorem RhinViola.reciprocalTailDifferenceHasSum (a : ℕ) :
    HasSum (fun k : ℕ =>
      (1 : ℝ) / (((k + a + 1 : ℕ) : ℝ)) -
        (1 : ℝ) / (((k + a + 2 : ℕ) : ℝ)))
      ((1 : ℝ) / (((a + 1 : ℕ) : ℝ))) := by sorry
