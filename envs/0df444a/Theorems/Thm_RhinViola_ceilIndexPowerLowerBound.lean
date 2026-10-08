-- Prove2me | Theorems.Thm_RhinViola_ceilIndexPowerLowerBound
-- name    : RhinViola.ceilIndexPowerLowerBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T11:36:27.521443+00:00
-- url     : https://prove2.me/theorems/fde8125e-b499-444b-91c3-398e7abe9a51
-- title:
--   Ceiling-index exponential bound converted to a power law
-- statement:
--   For u,c>0 and q>0, if n<log(2q)/u+1 then exp(-c)·2^(-c/u)·q^(-c/u)<exp(-cn). This converts the ceiling-index exponential lower bound in Rhin–Viola Lemma 4 into a fixed positive constant times the required power of q.
-- source:
--   Elementary exponential/power-law conversion used in G. Rhin and C. Viola, On the irrationality measure of ζ(2), Annales de l'Institut Fourier 43 (1993), pp. 91–92, Lemma 4.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem RhinViola.ceilIndexPowerLowerBound
    (u c : ℝ) (q n : ℕ)
    (hu : 0 < u) (hc : 0 < c) (hq : 0 < q)
    (hn : (n : ℝ) < Real.log (2 * (q : ℝ)) / u + 1) :
    Real.exp (-c) * (2 : ℝ) ^ (-(c / u)) *
        (q : ℝ) ^ (-(c / u)) <
      Real.exp (-(c * (n : ℝ))) := by sorry
