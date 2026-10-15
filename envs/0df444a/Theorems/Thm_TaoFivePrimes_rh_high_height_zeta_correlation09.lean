-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_zeta_correlation09
-- name    : TaoFivePrimes.rh_high_height_zeta_correlation09
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:01:03.952809+00:00
-- url     : https://prove2.me/theorems/fd10aaf7-2daa-40c9-9f67-9ec44d178112
-- title:
--   TaoFivePrimes.rh_high_height_zeta_correlation09
-- statement:
--   Exact verification of1025 unrounded complex binned correlations for Taylor order9, using the proposed128-bit global bin coefficients and proposed80-bit gamma DFT values. Three packed272-bit integer convolutions, unbiased with verified sums, are compared with the complete proposed output list. The gamma input magnitudes are also checked. This exact finite arithmetic theorem needs the separate binning, gamma-DFT soundness and analytic-error proofs before use in signs, a count or RH.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive09
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelationOutput09

theorem TaoFivePrimes.rh_high_height_zeta_correlation09 :
  RHHighZetaCorrelation.output 9 RHHighFFTPositive09.rows.flatten=
    RHHighZetaCorrelation.decode RHHighZetaCorrelationOutput09.rows.flatten ∧
  ∀ j:Nat,j<1954 → |(RHHighZetaCorrelation.sample RHHighFFTPositive09.rows.flatten j).1|≤(2:Int)^100 ∧
    |(RHHighZetaCorrelation.sample RHHighFFTPositive09.rows.flatten j).2|≤(2:Int)^100 := by sorry
