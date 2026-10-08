-- Prove2me | Theorems.Thm_RhinViola_unitIntervalOneSubPowIntegral
-- name    : RhinViola.unitIntervalOneSubPowIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T00:18:38.566072+00:00
-- url     : https://prove2.me/theorems/5928070f-3b41-4e9a-89f7-3226a02b2c5e
-- title:
--   Unit-interval integral of a reflected natural power
-- statement:
--   For every natural n, the integral of (1-x)^n over [0,1] is 1/(n+1). This is the reflected form of the standard monomial integral and is used in the finite harmonic evaluation of the J1 base integral in Rhin-Viola Lemma 2.
-- source:
--   Elementary reflected monomial integral used in the proof of G. Rhin and C. Viola, On the irrationality measure of zeta(2), Lemma 2, p. 88.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

theorem RhinViola.unitIntervalOneSubPowIntegral (n : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1, (1 - x) ^ n) =
      (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) := by sorry
