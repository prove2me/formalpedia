-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning13
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning13
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T04:42:00.31463+00:00
-- url     : https://prove2.me/theorems/e6fffcdf-4b0a-4cbb-8910-da19d4f8cf68
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning13
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms19969 through21504. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues13
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins13

theorem TaoFivePrimes.rh_high_height_dirichlet_binning13 :
  RHHighDirichletBinning.bins RHHighDirichletValues13.rows.flatten=
    RHHighDirichletBins13.values.map RHHighDirichletBinning.decode := by sorry
