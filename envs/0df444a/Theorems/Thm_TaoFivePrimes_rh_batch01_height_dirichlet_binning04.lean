-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning04
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning04
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T16:36:53.23061+00:00
-- url     : https://prove2.me/theorems/35e2bad1-2731-4d9b-ab23-4fcb5fe26a7d
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning04
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms6145 through7680. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues04
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins04

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning04 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues04.rows.flatten=
    RHBatch01DirichletBins04.values.map RHHighDirichletBinning.decode := by sorry
