-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning10
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning10
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:29:01.497131+00:00
-- url     : https://prove2.me/theorems/8a671003-c7b3-4fa6-bbe4-18edda2d0a62
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning10
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms15361 through16896. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues10
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins10

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning10 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues10.rows.flatten=
    RHBatch01DirichletBins10.values.map RHHighDirichletBinning.decode := by sorry
