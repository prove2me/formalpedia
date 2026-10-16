-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning31
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning31
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T21:53:55.234334+00:00
-- url     : https://prove2.me/theorems/703a5757-54b1-493d-a3f7-8d2817718ea8
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning31
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms47617 through49152. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues31
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins31

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning31 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues31.rows.flatten=
    RHBatch01DirichletBins31.values.map RHHighDirichletBinning.decode := by sorry
