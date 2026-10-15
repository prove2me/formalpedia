-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning18
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning18
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T05:19:44.772092+00:00
-- url     : https://prove2.me/theorems/a349dec5-735a-4490-90b8-ea918f414df2
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning18
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms27649 through29184. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues18
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins18

theorem TaoFivePrimes.rh_high_height_dirichlet_binning18 :
  RHHighDirichletBinning.bins RHHighDirichletValues18.rows.flatten=
    RHHighDirichletBins18.values.map RHHighDirichletBinning.decode := by sorry
