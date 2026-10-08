-- Prove2me | Theorems.Thm_RhinViola_unitSquareMonomialIntegral
-- name    : RhinViola.unitSquareMonomialIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T09:49:12.309699+00:00
-- url     : https://prove2.me/theorems/4db93d92-149e-4384-b5ad-50aa6f843e72
-- title:
--   Separated unit-square monomial integral
-- statement:
--   The iterated unit-square integral of x^a y^b separates into the product 1/(a+1) times 1/(b+1). This evaluates each term arising from the geometric expansion of 1/(1-xy).
-- source:
--   Elementary separated monomial integral used in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Section 3.

import Theorems.Thm_RhinViola_unitIntervalMonomialIntegral
import Mathlib.Tactic

theorem RhinViola.unitSquareMonomialIntegral (a b : ℕ) :
    (∫ x : ℝ in (0 : ℝ)..1,
      ∫ y : ℝ in (0 : ℝ)..1, x ^ a * y ^ b) =
      ((1 : ℝ) / (((a + 1 : ℕ) : ℝ))) *
        ((1 : ℝ) / (((b + 1 : ℕ) : ℝ))) := by sorry
