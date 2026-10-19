-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation14
-- name    : TaoFivePrimes.rh_batch01_height_zeta_correlation14
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T14:21:08.6258+00:00
-- url     : https://prove2.me/theorems/70c08310-6a68-40c7-9c18-e55774884d58
-- title:
--   TaoFivePrimes.rh_batch01_height_zeta_correlation14
-- statement:
--   Exact verification of1025 unrounded complex binned correlations for Taylor order14, using the proposed128-bit global bin coefficients and proposed80-bit gamma DFT values. Three packed272-bit integer convolutions, unbiased with verified sums, are compared with the complete proposed output list. The gamma input magnitudes are also checked. This exact finite arithmetic theorem needs the separate binning, gamma-DFT soundness and analytic-error proofs before use in signs, a count or RH.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive14
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput14

theorem TaoFivePrimes.rh_batch01_height_zeta_correlation14 :
  RHBatch01ZetaCorrelation.output 14 RHBatch01FFTPositive14.rows.flatten=
    RHBatch01ZetaCorrelation.decode RHBatch01ZetaCorrelationOutput14.rows.flatten ∧
  ∀ j:Nat,j<1954 → |(RHBatch01ZetaCorrelation.sample RHBatch01FFTPositive14.rows.flatten j).1|≤(2:Int)^100 ∧
    |(RHBatch01ZetaCorrelation.sample RHBatch01FFTPositive14.rows.flatten j).2|≤(2:Int)^100 := by sorry
