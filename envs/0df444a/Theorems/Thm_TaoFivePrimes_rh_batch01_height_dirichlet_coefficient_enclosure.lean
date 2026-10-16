-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_coefficient_enclosure
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_coefficient_enclosure
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:19:48.665863+00:00
-- url     : https://prove2.me/theorems/e372a16c-c61e-4e26-939c-57c59291380c
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_coefficient_enclosure
-- statement:
--   Uniform analytic enclosure of every proposed normalized Dirichlet coefficient for n=1..50000 and Taylor orders0..23, with error at most10^(-24). The bin offset has absolute value at most1/2 and the bin index is at most928. The proof combines the accepted exact finite guards with logarithm, phase, exponential, dyadic power and rounding estimates. No endpoint sign, zero count or RH assertion.
-- source:
--   Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletArithmetic

theorem TaoFivePrimes.rh_batch01_height_dirichlet_coefficient_enclosure (n k : Nat) (hn:1 ≤ n ∧ n≤50000) (hk:k<24) :
  let L:ℝ:=Real.log (n:ℝ)+Real.log Real.pi/2
  let d:ℝ:=512*L/(2*Real.pi)-(RHBatch01DirichletArithmetic.bin n:ℝ)
  let c:=RHBatch01DirichletArithmetic.coefficient n k
  ‖((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128-
    Complex.exp (-(1/2+Complex.I*(3289999808:ℂ))*(L:ℂ))*(d:ℂ)^k‖≤1/10^24 ∧
    |d|≤1/2 ∧ RHBatch01DirichletArithmetic.bin n≤928 := by sorry
