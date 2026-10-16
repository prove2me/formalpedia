-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning30
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning30
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T21:43:19.321464+00:00
-- url     : https://prove2.me/theorems/70962a1a-11e8-40dc-9a90-2b072425348b
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning30
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms46081 through47616. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues30
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins30

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning30 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues30.rows.flatten=
    RHBatch01DirichletBins30.values.map RHHighDirichletBinning.decode := by sorry
