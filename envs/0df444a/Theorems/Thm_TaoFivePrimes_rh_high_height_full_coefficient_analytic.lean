-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_full_coefficient_analytic
-- name    : TaoFivePrimes.rh_high_height_full_coefficient_analytic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:07:42.639973+00:00
-- url     : https://prove2.me/theorems/62e084e0-7f22-4602-a164-44a7bcf9ae8c
-- title:
--   TaoFivePrimes.rh_high_height_full_coefficient_analytic
-- statement:
--   Combines the accepted finite Dirichlet truncation, normalized gamma Taylor formula and grouped bin errors: gamma moment sample bounds and errors imply a3e-15 bound for the actual window Fourier coefficient versus the explicit grouped sum divided by512. The finite correlation and coefficient assembly equalities remain explicit requirements for the final polynomial coefficient enclosure.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighCoefficientFunctions
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_full_coefficient_analytic (m : Nat) (hm:m≤1024) (G : Nat→Nat→ℂ)
 (hF:∀b:Nat,b<929 → ∀k:Nat,k<24 → ‖RHHighFullCoefficient.F m b k‖≤65537)
 (heF:∀b:Nat,b<929 → ∀k:Nat,k<24 → ‖RHHighFullCoefficient.F m b k-G b k‖≤1/10^15) :
 ‖(1/512:ℂ)*𝓕 RHHighFullCoefficient.W ((m:ℝ)/512)-(1/512:ℂ)*RHHighFullCoefficient.group G‖≤3/10^15 := by sorry
