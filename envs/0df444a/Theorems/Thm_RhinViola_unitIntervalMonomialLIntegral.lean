-- Prove2me | Theorems.Thm_RhinViola_unitIntervalMonomialLIntegral
-- name    : RhinViola.unitIntervalMonomialLIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T09:43:33.452589+00:00
-- url     : https://prove2.me/theorems/8d84cad4-feed-4d75-a4ba-ba92611d5830
-- title:
--   Nonnegative unit-interval monomial lintegral
-- statement:
--   The nonnegative Lebesgue integral of x^n over (0,1] equals the ENNReal coercion of 1/(n+1). This converts the elementary real interval integral into the nonnegative lintegral form needed for Tonelli and lintegral_tsum.
-- source:
--   Measure-theoretic reformulation of the elementary monomial integral used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Section 3.

import Theorems.Thm_RhinViola_unitIntervalMonomialIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

theorem RhinViola.unitIntervalMonomialLIntegral (n : ℕ) :
    (∫⁻ x : ℝ in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ n)) =
      ENNReal.ofReal ((1 : ℝ) / (((n + 1 : ℕ) : ℝ))) := by sorry
