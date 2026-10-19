-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation06
-- name    : TaoFivePrimes.rh_batch01_height_zeta_correlation06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T10:40:27.493982+00:00
-- url     : https://prove2.me/theorems/b27b3a94-b4fc-4249-b7eb-c91f7c98172a
-- title:
--   TaoFivePrimes.rh_batch01_height_zeta_correlation06
-- statement:
--   Exact verification of1025 unrounded complex binned correlations for Taylor order6, using the proposed128-bit global bin coefficients and proposed80-bit gamma DFT values. Three packed272-bit integer convolutions, unbiased with verified sums, are compared with the complete proposed output list. The gamma input magnitudes are also checked. This exact finite arithmetic theorem needs the separate binning, gamma-DFT soundness and analytic-error proofs before use in signs, a count or RH.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive06
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput06

theorem TaoFivePrimes.rh_batch01_height_zeta_correlation06 :
  RHBatch01ZetaCorrelation.output 6 RHBatch01FFTPositive06.rows.flatten=
    RHBatch01ZetaCorrelation.decode RHBatch01ZetaCorrelationOutput06.rows.flatten ∧
  ∀ j:Nat,j<1954 → |(RHBatch01ZetaCorrelation.sample RHBatch01FFTPositive06.rows.flatten j).1|≤(2:Int)^100 ∧
    |(RHBatch01ZetaCorrelation.sample RHBatch01FFTPositive06.rows.flatten j).2|≤(2:Int)^100 := by sorry
