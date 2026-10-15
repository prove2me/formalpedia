-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning08
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning08
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T04:17:24.259695+00:00
-- url     : https://prove2.me/theorems/c976b529-313a-449b-ab1a-e4cc9c9707a6
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning08
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms12289 through13824. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues08
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins08

theorem TaoFivePrimes.rh_high_height_dirichlet_binning08 :
  RHHighDirichletBinning.bins RHHighDirichletValues08.rows.flatten=
    RHHighDirichletBins08.values.map RHHighDirichletBinning.decode := by sorry
