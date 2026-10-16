-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning25
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning25
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:37:03.023771+00:00
-- url     : https://prove2.me/theorems/1d9c8300-3cd0-49bb-996a-610511601605
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning25
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms38401 through39936. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues25
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins25

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning25 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues25.rows.flatten=
    RHBatch01DirichletBins25.values.map RHHighDirichletBinning.decode := by sorry
