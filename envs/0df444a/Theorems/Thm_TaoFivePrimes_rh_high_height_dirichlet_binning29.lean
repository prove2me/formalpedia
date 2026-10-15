-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning29
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning29
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:17:02.300559+00:00
-- url     : https://prove2.me/theorems/235cd221-d310-45a7-89b2-b7834e09a4b1
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning29
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms44545 through46080. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues29
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins29

theorem TaoFivePrimes.rh_high_height_dirichlet_binning29 :
  RHHighDirichletBinning.bins RHHighDirichletValues29.rows.flatten=
    RHHighDirichletBins29.values.map RHHighDirichletBinning.decode := by sorry
