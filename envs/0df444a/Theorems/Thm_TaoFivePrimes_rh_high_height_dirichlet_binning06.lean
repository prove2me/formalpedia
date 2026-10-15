-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_binning06
-- name    : TaoFivePrimes.rh_high_height_dirichlet_binning06
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T04:08:35.847985+00:00
-- url     : https://prove2.me/theorems/7b951ec7-040a-40fd-af31-258c953de9f1
-- title:
--   TaoFivePrimes.rh_high_height_dirichlet_binning06
-- statement:
--   Exact accumulation of24 normalized Taylor coefficients from the proposed128-bit weight components and bin offsets for Dirichlet terms9217 through10752. Each ordinary integer offset power is rounded as in the defined algorithm. This theorem asserts an exact finite equality and requires the separate accepted input-arithmetic and analytic bounds before use in Fourier reconstruction.
-- source:
--   Platt DOI10.1090/mcom/3198, binned Taylor/Fourier reconstruction. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletBinning
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues06
import Definitions.Def_TaoFivePrimes_RHHighDirichletBins06

theorem TaoFivePrimes.rh_high_height_dirichlet_binning06 :
  RHHighDirichletBinning.bins RHHighDirichletValues06.rows.flatten=
    RHHighDirichletBins06.values.map RHHighDirichletBinning.decode := by sorry
