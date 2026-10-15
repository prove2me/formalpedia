-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning10
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning10
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T04:23:53.005232+00:00
-- url     : https://prove2.me/theorems/f47ada69-6779-40e3-9ada-712df2f97253
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning10
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms15361 through16896. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues10
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins10

theorem TaoFivePrimes.rh_high_height_dirichlet_binning10 :
  RHHighDirichletBinning.bins RHHighDirichletValues10.rows.flatten=
    RHHighDirichletBins10.values.map RHHighDirichletBinning.decode := by sorry
