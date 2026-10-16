-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning29
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning29
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T21:34:39.432975+00:00
-- url     : https://prove2.me/theorems/7a628da2-f205-424b-9920-e89bab4ada89
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning29
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms44545 through46080. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues29
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins29

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning29 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues29.rows.flatten=
    RHBatch01DirichletBins29.values.map RHHighDirichletBinning.decode := by sorry
