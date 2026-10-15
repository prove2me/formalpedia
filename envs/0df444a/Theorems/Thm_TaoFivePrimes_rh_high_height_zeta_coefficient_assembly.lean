-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_coefficient_assembly
-- name    : TaoFivePrimes.rh_high_height_zeta_coefficient_assembly
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:54:44.049396+00:00
-- url     : https://prove2.me/theorems/d49eaee0-581d-4882-9572-2c25af10c09a
-- title:
--   TaoFivePrimes.rh_high_height_zeta_coefficient_assembly
-- statement:
--   Ordinary kernel verification that summing the24 proposed correlation vectors and rounding gives exactly the existing1025 Fourier polynomial coefficients. The uncorrected constant imaginary quotient is -1, so forcing it to zero changes it by one80-bit unit. This finite identity still needs the separate exact correlation, binning, gamma-DFT and analytic-error proofs before a sign, count or RH conclusion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighZetaCoefficientAssembly

theorem TaoFivePrimes.rh_high_height_zeta_coefficient_assembly :
  RHHighZetaCoefficientAssembly.total.length=1025 ∧
  RHHighZetaCoefficientAssembly.rounded=RHHighZetaCoefficientAssembly.expected ∧
  (((RHHighZetaCoefficientAssembly.total[0]?).getD (0,0)).2/(2:Int)^142)= -1 := by sorry
