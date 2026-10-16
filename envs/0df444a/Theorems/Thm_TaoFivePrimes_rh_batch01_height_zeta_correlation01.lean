-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_zeta_correlation01
-- name    : TaoFivePrimes.rh_batch01_height_zeta_correlation01
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:30:31.328655+00:00
-- url     : https://prove2.me/theorems/93b5d6f2-52eb-4a93-84c1-3b6b373ce5ca
-- title:
--   TaoFivePrimes.rh_batch01_height_zeta_correlation01
-- statement:
--   Exact verification of1025 unrounded complex binned correlations for Taylor order1, using the proposed128-bit global bin coefficients and proposed80-bit gamma DFT values. Three packed272-bit integer convolutions, unbiased with verified sums, are compared with the complete proposed output list. The gamma input magnitudes are also checked. This exact finite arithmetic theorem needs the separate binning, gamma-DFT soundness and analytic-error proofs before use in signs, a count or RH.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive01
import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelationOutput01

theorem TaoFivePrimes.rh_batch01_height_zeta_correlation01 :
  RHBatch01ZetaCorrelation.output 1 RHBatch01FFTPositive01.rows.flatten=
    RHBatch01ZetaCorrelation.decode RHBatch01ZetaCorrelationOutput01.rows.flatten ∧
  ∀ j:Nat,j<1954 → |(RHBatch01ZetaCorrelation.sample RHBatch01FFTPositive01.rows.flatten j).1|≤(2:Int)^100 ∧
    |(RHBatch01ZetaCorrelation.sample RHBatch01FFTPositive01.rows.flatten j).2|≤(2:Int)^100 := by sorry
