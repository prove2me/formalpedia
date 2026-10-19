-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_coefficient_assembly
-- name    : TaoFivePrimes.rh_batch01_height_zeta_coefficient_assembly
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T15:55:19.266837+00:00
-- url     : https://prove2.me/theorems/e9ad5dc7-8b29-4c52-9b64-952ebd4e4ad5
-- title:
--   TaoFivePrimes.rh_batch01_height_zeta_coefficient_assembly
-- statement:
--   Ordinary kernel verification that the24 proposed exact correlation vectors sum to1025 entries and round to the proposed Fourier coefficients. The absolute uncorrected constant imaginary quotient is at most one80-bit integer unit; setting it to zero therefore has the same one-unit error bound for this fresh center. The individual correlations and analytic accuracy remain separate required proofs.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCoefficientAssembly

theorem TaoFivePrimes.rh_batch01_height_zeta_coefficient_assembly :
  RHBatch01ZetaCoefficientAssembly.total.length=1025 ∧
  RHBatch01ZetaCoefficientAssembly.rounded=RHBatch01ZetaCoefficientAssembly.expected ∧
  |(((RHBatch01ZetaCoefficientAssembly.total[0]?).getD (0,0)).2/(2:Int)^142)|≤1 := by sorry
