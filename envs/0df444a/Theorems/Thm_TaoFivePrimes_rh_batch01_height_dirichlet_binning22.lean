-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning22
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning22
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:06:45.654776+00:00
-- url     : https://prove2.me/theorems/393d9e11-4d3e-4e1c-af2a-0e105745e5e0
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning22
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms33793 through35328. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues22
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins22

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning22 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues22.rows.flatten=
    RHBatch01DirichletBins22.values.map RHHighDirichletBinning.decode := by sorry
