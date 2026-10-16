-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning28
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning28
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T21:22:26.378826+00:00
-- url     : https://prove2.me/theorems/8dbc4708-23bf-4547-90f3-7efd8218dd97
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning28
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms43009 through44544. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues28
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins28

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning28 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues28.rows.flatten=
    RHBatch01DirichletBins28.values.map RHHighDirichletBinning.decode := by sorry
