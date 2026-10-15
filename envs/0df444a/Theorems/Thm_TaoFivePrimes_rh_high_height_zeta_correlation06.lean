-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation06
-- name    : TaoFivePrimes.rh_high_height_zeta_correlation06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:33:59.261384+00:00
-- url     : https://prove2.me/theorems/e259a0d7-06a7-417d-9087-482493ad0c58
-- title:
--   TaoFivePrimes.rh_high_height_zeta_correlation06
-- statement:
--   Exact verification of1025 unrounded complex binned correlations for Taylor order6, using the proposed128-bit global bin coefficients and proposed80-bit gamma DFT values. Three packed272-bit integer convolutions, unbiased with verified sums, are compared with the complete proposed output list. The gamma input magnitudes are also checked. This exact finite arithmetic theorem needs the separate binning, gamma-DFT soundness and analytic-error proofs before use in signs, a count or RH.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive06
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput06

theorem TaoFivePrimes.rh_high_height_zeta_correlation06 :
  RHHighZetaCorrelation.output 6 RHHighFFTPositive06.rows.flatten=
    RHHighZetaCorrelation.decode RHHighZetaCorrelationOutput06.rows.flatten ∧
  ∀ j:Nat,j<1954 → |(RHHighZetaCorrelation.sample RHHighFFTPositive06.rows.flatten j).1|≤(2:Int)^100 ∧
    |(RHHighZetaCorrelation.sample RHHighFFTPositive06.rows.flatten j).2|≤(2:Int)^100 := by sorry
