-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning07
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning07
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T16:57:39.000634+00:00
-- url     : https://prove2.me/theorems/38a491af-832d-42f5-825f-23c9b7e8eed2
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning07
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms10753 through12288. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues07
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins07

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning07 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues07.rows.flatten=
    RHBatch01DirichletBins07.values.map RHHighDirichletBinning.decode := by sorry
