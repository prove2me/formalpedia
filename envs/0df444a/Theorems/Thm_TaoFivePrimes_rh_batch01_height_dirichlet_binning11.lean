-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning11
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning11
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:46:25.122995+00:00
-- url     : https://prove2.me/theorems/c6a095c1-f7f0-48f1-be01-d5dfe9976bd5
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning11
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms16897 through18432. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues11
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins11

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning11 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues11.rows.flatten=
    RHBatch01DirichletBins11.values.map RHHighDirichletBinning.decode := by sorry
