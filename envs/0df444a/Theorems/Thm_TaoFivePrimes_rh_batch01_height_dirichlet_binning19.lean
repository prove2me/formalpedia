-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning19
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning19
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T19:46:14.639817+00:00
-- url     : https://prove2.me/theorems/ce16454a-5213-4af2-8c6f-d28c1f3eac04
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning19
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms29185 through30720. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues19
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins19

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning19 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues19.rows.flatten=
    RHBatch01DirichletBins19.values.map RHHighDirichletBinning.decode := by sorry
