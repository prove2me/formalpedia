-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning07
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning07
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T04:12:51.317173+00:00
-- url     : https://prove2.me/theorems/d0ad8626-3c42-479b-b2f4-bfa4918dc319
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning07
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms10753 through12288. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues07
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins07

theorem TaoFivePrimes.rh_high_height_dirichlet_binning07 :
  RHHighDirichletBinning.bins RHHighDirichletValues07.rows.flatten=
    RHHighDirichletBins07.values.map RHHighDirichletBinning.decode := by sorry
