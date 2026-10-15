-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation13
-- name    : TaoFivePrimes.rh_high_height_zeta_correlation13
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:30:53.463137+00:00
-- url     : https://prove2.me/theorems/5f0abe63-0ac5-4c61-b89d-cfdbf6044470
-- title:
--   TaoFivePrimes.rh_high_height_zeta_correlation13
-- statement:
--   Exact verification of1025 unrounded complex binned correlations for Taylor order13, using the proposed128-bit global bin coefficients and proposed80-bit gamma DFT values. Three packed272-bit integer convolutions, unbiased with verified sums, are compared with the complete proposed output list. The gamma input magnitudes are also checked. This exact finite arithmetic theorem needs the separate binning, gamma-DFT soundness and analytic-error proofs before use in signs, a count or RH.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive13
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput13

theorem TaoFivePrimes.rh_high_height_zeta_correlation13 :
  RHHighZetaCorrelation.output 13 RHHighFFTPositive13.rows.flatten=
    RHHighZetaCorrelation.decode RHHighZetaCorrelationOutput13.rows.flatten ∧
  ∀ j:Nat,j<1954 → |(RHHighZetaCorrelation.sample RHHighFFTPositive13.rows.flatten j).1|≤(2:Int)^100 ∧
    |(RHHighZetaCorrelation.sample RHHighFFTPositive13.rows.flatten j).2|≤(2:Int)^100 := by sorry
