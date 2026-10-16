-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_dirichlet_binning32
-- name    : TaoFivePrimes.rh_batch01_height_dirichlet_binning32
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T22:01:00.402174+00:00
-- url     : https://prove2.me/theorems/9faed5c7-0b04-4ec7-9851-84a75ef0eca9
-- title:
--   TaoFivePrimes.rh_batch01_height_dirichlet_binning32
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms49153 through50000. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues32
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletBins32

theorem TaoFivePrimes.rh_batch01_height_dirichlet_binning32 :
  RHHighDirichletBinning.bins RHBatch01DirichletValues32.rows.flatten=
    RHBatch01DirichletBins32.values.map RHHighDirichletBinning.decode := by sorry
