-- Prove2me | Theorems.Thm_RhinViola_unitIntervalMonomialIntegral
-- name    : RhinViola.unitIntervalMonomialIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T23:43:01.496896+00:00
-- url     : https://prove2.me/theorems/3423927a-2320-4927-af83-28c755c2028b
-- title:
--   Exact unit-interval monomial integral
-- statement:
--   For every natural n, the integral of x^n from 0 to 1 is exactly 1/(n+1). This is the one-dimensional factor used in each monomial term of the Rhin-Viola double-integral expansion.
-- source:
--   Elementary calculus identity used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

theorem RhinViola.unitIntervalMonomialIntegral (n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, x ^ n) =
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) := by sorry
